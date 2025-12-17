// SPDX-License-Identifier: MIT
//
// Little-endian binary reader with alignment helpers.

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt};
use std::io::{Cursor, Read, Seek, SeekFrom};

pub struct Reader<'a> {
    cur: Cursor<&'a [u8]>,
}

impl<'a> Reader<'a> {
    pub fn new(buf: &'a [u8]) -> Self {
        Self { cur: Cursor::new(buf) }
    }

    pub fn pos(&mut self) -> Result<u64> {
        Ok(self.cur.stream_position()?)
    }

    pub fn seek(&mut self, pos: u64) -> Result<()> {
        self.cur.seek(SeekFrom::Start(pos))?;
        Ok(())
    }

    pub fn align(&mut self, n: u64) -> Result<()> {
        if n == 0 {
            return Ok(());
        }
        let p = self.pos()?;
        let rem = p % n;
        if rem != 0 {
            self.seek(p + (n - rem))?;
        }
        Ok(())
    }

    pub fn read_u8(&mut self) -> Result<u8> {
        Ok(self.cur.read_u8()?)
    }

    pub fn read_i16(&mut self) -> Result<i16> {
        Ok(self.cur.read_i16::<LittleEndian>()?)
    }

    pub fn read_u16(&mut self) -> Result<u16> {
        Ok(self.cur.read_u16::<LittleEndian>()?)
    }

    pub fn read_i32(&mut self) -> Result<i32> {
        Ok(self.cur.read_i32::<LittleEndian>()?)
    }

    pub fn read_u32(&mut self) -> Result<u32> {
        Ok(self.cur.read_u32::<LittleEndian>()?)
    }

    pub fn read_i64(&mut self) -> Result<i64> {
        Ok(self.cur.read_i64::<LittleEndian>()?)
    }

    pub fn read_f64(&mut self) -> Result<f64> {
        Ok(self.cur.read_f64::<LittleEndian>()?)
    }

    pub fn read_exact(&mut self, n: usize) -> Result<Vec<u8>> {
        let mut v = vec![0u8; n];
        self.cur.read_exact(&mut v)?;
        Ok(v)
    }

    pub fn read_fourcc(&mut self) -> Result<[u8; 4]> {
        let v = self.read_exact(4)?;
        Ok([v[0], v[1], v[2], v[3]])
    }

    pub fn expect_fourcc(&mut self, expect: &[u8; 4]) -> Result<()> {
        let got = self.read_fourcc()?;
        if &got != expect {
            anyhow::bail!("fourcc mismatch: expect {:?}, got {:?}", expect, got);
        }
        Ok(())
    }
}
