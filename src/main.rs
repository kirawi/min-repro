mod combinators;
use combinators::*;

use std::{
    io::{Read, Seek, SeekFrom, Write},
    num::NonZeroUsize,
    path::Path,
    sync::Arc,
    time::{Duration, SystemTime},
};

struct History {
    revisions: Vec<Revision>,
    current: usize,
}

struct Revision {
    parent: usize,
    last_child: Option<NonZeroUsize>,
    transaction: Arc<Transaction>,
    inversion: Arc<Transaction>,
    timestamp: SystemTime,
}

#[derive(Default, PartialEq)]
struct Transaction {
    changes: ChangeSet,
    selection: Option<Selection>,
}

#[derive(Default, PartialEq)]
pub struct ChangeSet {
    changes: Vec<Operation>,
    len: usize,
    len_after: usize,
}

#[derive(PartialEq)]
pub enum Operation {
    Retain(usize),
    Delete(usize),
    Insert(String),
}

#[derive(PartialEq)]
pub struct Selection {
    ranges: Vec<Range>,
    primary_index: usize,
}

#[derive(PartialEq)]
pub struct Range {
    pub anchor: usize,
    pub head: usize,
    pub old_visual_position: Option<(u32, u32)>,
}

impl Default for History {
    fn default() -> Self {
        Self {
            revisions: vec![Revision {
                parent: 0,
                last_child: None,
                transaction: Arc::new(Transaction::default()),
                inversion: Arc::new(Transaction::default()),
                timestamp: SystemTime::now(),
            }],
            current: 0,
        }
    }
}

#[derive(Debug)]
pub enum StateError {
    Outdated,
    InvalidHeader,
    InvalidOffset,
    InvalidData(String),
    InvalidTree,
    InvalidHash,
    Other(anyhow::Error),
}

impl std::fmt::Display for StateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Outdated => f.write_str("Outdated file"),
            Self::InvalidHeader => f.write_str("Invalid undofile header"),
            Self::InvalidOffset => f.write_str("Invalid merge offset"),
            Self::InvalidData(msg) => f.write_str(msg),
            Self::InvalidTree => f.write_str("not a tree"),
            Self::InvalidHash => f.write_str("invalid hash for undofile itself"),
            Self::Other(e) => e.fmt(f),
        }
    }
}

impl From<std::io::Error> for StateError {
    fn from(value: std::io::Error) -> Self {
        Self::Other(value.into())
    }
}

impl From<std::time::SystemTimeError> for StateError {
    fn from(value: std::time::SystemTimeError) -> Self {
        Self::Other(value.into())
    }
}

impl From<anyhow::Error> for StateError {
    fn from(value: anyhow::Error) -> Self {
        Self::Other(value)
    }
}

impl std::error::Error for StateError {}

const UNDO_FILE_HEADER_TAG: &[u8] = b"Helix";
const UNDO_FILE_HEADER_LEN: usize = UNDO_FILE_HEADER_TAG.len();
const UNDO_FILE_VERSION: u8 = 1;

fn get_hash<R: Read>(reader: &mut R) -> std::io::Result<[u8; sha1_smol::DIGEST_LENGTH]> {
    const BUF_SIZE: usize = 8192;

    let mut buf = [0u8; BUF_SIZE];
    let mut hash = sha1_smol::Sha1::new();
    loop {
        let total_read = reader.read(&mut buf)?;
        if total_read == 0 {
            break;
        }

        hash.update(&buf[0..total_read]);
    }
    Ok(hash.digest().bytes())
}
impl History {
    pub fn serialize<W: Write + Seek>(
        &self,
        writer: &mut W,
        path: &Path,
        revision: usize,
        last_saved_revision: usize,
    ) -> Result<(), StateError> {
        // Header
        let mtime = std::fs::metadata(path)?
            .modified()?
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        writer.write(UNDO_FILE_HEADER_TAG)?;
        write_byte(writer, UNDO_FILE_VERSION)?;
        write_usize(writer, self.current)?;
        write_usize(writer, revision)?;
        write_u64(writer, mtime)?;
        writer.write_all(&get_hash(&mut std::fs::File::open(path)?)?)?;

        // Append new revisions to the end of the file.
        // TODO: Recompute hash on append
        write_usize(writer, self.revisions.len())?;
        writer.seek(SeekFrom::End(0))?;
        for rev in &self.revisions[last_saved_revision..] {
            rev.serialize(writer)?;
        }

        Ok(())
    }

    /// Returns the deserialized [`History`] and the last_saved_revision.
    pub fn deserialize<R: Read>(reader: &mut R, path: &Path) -> anyhow::Result<(usize, Self)> {
        let (current, last_saved_revision) = Self::read_header(reader, path)?;

        // Read the revisions and construct the tree.
        let len = read_usize(reader)?;
        let mut revisions: Vec<Revision> = Vec::with_capacity(len);
        for _ in 0..len {
            let rev = Revision::deserialize(reader)?;
            let len = revisions.len();
            match revisions.get_mut(rev.parent) {
                Some(r) => r.last_child = NonZeroUsize::new(len),
                None if len != 0 => {
                    anyhow::bail!(StateError::InvalidData(format!(
                        "non-contiguous history: {} >= {}",
                        rev.parent, len
                    )));
                }
                None => {
                    // Starting revision check
                    let default_rev = History::default().revisions.pop().unwrap();
                    if rev != default_rev {
                        anyhow::bail!(StateError::InvalidData(String::from(
                            "Missing 0th revision"
                        )));
                    }
                }
            }
            revisions.push(rev);
        }

        let history = History { current, revisions };
        Ok((last_saved_revision, history))
    }

    pub fn read_header<R: Read>(reader: &mut R, path: &Path) -> anyhow::Result<(usize, usize)> {
        let header: [u8; UNDO_FILE_HEADER_LEN] = read_many_bytes(reader)?;
        let version = read_byte(reader)?;
        if header != UNDO_FILE_HEADER_TAG || version != UNDO_FILE_VERSION {
            Err(anyhow::anyhow!(StateError::InvalidHeader))
        } else {
            let current = read_usize(reader)?;
            let last_saved_revision = read_usize(reader)?;
            let mtime = read_u64(reader)?;
            let last_mtime = std::fs::metadata(path)?
                .modified()?
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs();
            let mut hash = [0u8; sha1_smol::DIGEST_LENGTH];
            reader.read_exact(&mut hash)?;

            if mtime != last_mtime && hash != get_hash(&mut std::fs::File::open(path)?)? {
                anyhow::bail!(StateError::Outdated);
            }

            // Tree hash
            Ok((current, last_saved_revision))
        }
    }
}

impl PartialEq for Revision {
    fn eq(&self, other: &Self) -> bool {
        self.parent == other.parent
            && self.last_child == other.last_child
            && self.transaction == other.transaction
            && self.inversion == other.inversion
    }
}
impl Revision {
    fn serialize<W: Write>(&self, writer: &mut W) -> anyhow::Result<()> {
        write_usize(writer, self.parent)?;
        self.transaction.serialize(writer)?;
        self.inversion.serialize(writer)?;
        write_u64(
            writer,
            self.timestamp
                .duration_since(std::time::UNIX_EPOCH)?
                .as_secs(),
        )?;

        Ok(())
    }

    fn deserialize<R: Read>(reader: &mut R) -> anyhow::Result<Self> {
        let parent = read_usize(reader)?;
        let transaction = Arc::new(Transaction::deserialize(reader)?);
        let inversion = Arc::new(Transaction::deserialize(reader)?);
        let timestamp = std::time::UNIX_EPOCH
            .checked_add(Duration::from_secs(read_u64(reader)?))
            .unwrap_or_else(SystemTime::now);
        Ok(Revision {
            parent,
            last_child: None,
            transaction,
            inversion,
            timestamp,
        })
    }
}

impl Transaction {
    pub fn serialize<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        write_option(writer, self.selection.as_ref(), |writer, selection| {
            selection.serialize(writer)
        })?;

        write_usize(writer, self.changes.len)?;
        write_usize(writer, self.changes.len_after)?;
        write_vec(writer, &self.changes.changes, |writer, operation| {
            let variant = match operation {
                Operation::Retain(_) => 0,
                Operation::Delete(_) => 1,
                Operation::Insert(_) => 2,
            };
            write_byte(writer, variant)?;
            match operation {
                Operation::Retain(n) | Operation::Delete(n) => {
                    write_usize(writer, *n)?;
                }

                Operation::Insert(tendril) => {
                    write_string(writer, tendril.as_str())?;
                }
            }

            Ok(())
        })?;

        Ok(())
    }

    pub fn deserialize<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let selection = read_option(reader, Selection::deserialize)?;

        let len = read_usize(reader)?;
        let len_after = read_usize(reader)?;
        let changes = read_vec(reader, |reader| {
            let res = match read_byte(reader)? {
                0 => Operation::Retain(read_usize(reader)?),
                1 => Operation::Delete(read_usize(reader)?),
                2 => Operation::Insert(read_string(reader)?.into()),
                _ => {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::Other,
                        "invalid variant",
                    ))
                }
            };
            Ok(res)
        })?;
        let changes = ChangeSet {
            changes,
            len,
            len_after,
        };

        Ok(Transaction { changes, selection })
    }
}

impl Selection {
    pub fn serialize<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        write_usize(writer, self.primary_index)?;
        write_vec(writer, &self.ranges, |writer, range| {
            write_usize(writer, range.anchor)?;
            write_usize(writer, range.head)?;
            write_option(writer, range.old_visual_position.as_ref(), |writer, pos| {
                write_u32(writer, pos.0)?;
                write_u32(writer, pos.1)?;
                Ok(())
            })?;
            Ok(())
        })?;

        Ok(())
    }

    pub fn deserialize<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let primary_index = read_usize(reader)?;
        let ranges = read_vec(reader, |reader| {
            let anchor = read_usize(reader)?;
            let head = read_usize(reader)?;
            let old_visual_position = read_option(reader, |reader| {
                let res = (read_u32(reader)?, read_u32(reader)?);
                Ok(res)
            })?;
            Ok(Range {
                anchor,
                head,
                old_visual_position,
            })
        })?;
        Ok(Self {
            ranges: ranges.into(),
            primary_index,
        })
    }
}

fn main() {}

#[cfg(test)]
mod test {
    use std::io::Read;

    use super::*;

    quickcheck::quickcheck! {
        fn random_undofile(inserts: Vec<String>) -> bool {
            use std::io::Write;
            // let (orig_hist, doc) = generate_history(inserts);
            let orig_hist = History::default();
            let mut file = tempfile::NamedTempFile::new().unwrap();
            file.write_all(b"").unwrap();
            // file.write_all(&doc.bytes().collect::<Vec<_>>()).unwrap();
            let mut undofile = tempfile::NamedTempFile::new().unwrap();

            let mut u = std::io::Cursor::new(Vec::new());
            orig_hist
                .serialize(&mut u, file.path(), orig_hist.revisions.len(), 0)
                .unwrap();
            let u = u.into_inner();
            undofile.write_all(&u).unwrap();
            let mut n = Vec::new();
            undofile.read_to_end(&mut n).unwrap();
            assert_eq!(u, n);
            let (_, de_hist) = History::deserialize(&mut undofile, file.path())
                .map_err(|_| {
                    panic!("{:?}", undofile.bytes().take(5).collect::<Vec<_>>());
                })
                .unwrap();
            orig_hist.revisions.len() == de_hist.revisions.len()
                && orig_hist
                    .revisions
                    .iter()
                    .zip(de_hist.revisions.iter())
                    .all(|(a, b)| {
                        a.parent == b.parent
                            && a.transaction == b.transaction
                            && a.inversion == b.inversion
                    })
        }
    }
}
