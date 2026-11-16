//! The newline table, [`LineStarts`] (`docs/token-pipeline-soa-plan.md`, D3).

/// A 1-based line and a 0-based column, in [`LineStarts`]'s sense: FCS's
/// source position.
///
/// The column counts UTF-16 code units from the line's start, as FCS's
/// lexbuf does (it reads the source as a .NET string): `é` advances it by one
/// and `𝔸`, a surrogate pair, by two. Every offside comparison is made in that
/// scale, so a column must never be a byte count. [`LineStarts::byte_offset`]
/// recovers a position's byte offset.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LinePos {
    pub line: u32,
    pub col: u32,
}

/// The first byte of every line of one source, in FCS's sense, beside the
/// source it indexes.
///
/// FCS breaks lines at `newline = '\n' | '\r' '\n'` (`lex.fsl:315`), so the
/// byte after every `\n` starts a line, and a lone `\r` starts none. That
/// holds wherever the `\n` sits: FCS's lexbuf counts the breaks inside block
/// comments, strings and inactive `#if` regions too, which no token of the
/// lexer's marks. So the table is computed from the bytes, not from tokens.
///
/// FCS strips a file-start UTF-8 BOM before it counts columns, so line 1
/// starts past one. A `U+FEFF` anywhere else is an ordinary character.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LineStarts<'s> {
    /// The source, read for [`Self::byte_offset`].
    source: &'s str,
    /// `starts[i]` is line `i + 1`'s first byte: past a file-start BOM for
    /// line 1, else one past a `\n`. Strictly ascending, and never empty.
    starts: Vec<u32>,
    /// Every non-ASCII character, in source order: its first byte, and the
    /// bytes its UTF-8 spends beyond its UTF-16 code units, summed over it and
    /// every non-ASCII character before it. A column is then the bytes from
    /// the line's start less the excess between there and the offset, and an
    /// ASCII source, the common case, leaves this empty.
    wide: Vec<(u32, u32)>,
}

/// [`LineStarts::wide`] of the UTF-8 `bytes`. A non-ASCII character starts at
/// a lead byte (`0xC0` and up); a two-byte one spends one byte beyond its one
/// UTF-16 unit, a three-byte one two, and a four-byte one, two units, two.
/// Found as [`LineStarts::new`] finds `\n`s: a chunk's lead bytes as a bit
/// mask, then one push per set bit.
fn wide_chars(bytes: &[u8]) -> Vec<(u32, u32)> {
    const CHUNK: usize = 32;
    let mut wide = Vec::new();
    let mut excess = 0u32;
    let mut push = |at: u32, lead: u8| {
        excess += if lead < 0xE0 { 1 } else { 2 };
        wide.push((at, excess));
    };
    let (chunks, tail) = bytes.as_chunks::<CHUNK>();
    let mut base = 0u32;
    for chunk in chunks {
        let mut mask = 0u32;
        for (j, &b) in chunk.iter().enumerate() {
            mask |= u32::from(b >= 0xC0) << j;
        }
        while mask != 0 {
            let j = mask.trailing_zeros();
            push(base + j, chunk[j as usize]);
            mask &= mask - 1;
        }
        base += CHUNK as u32;
    }
    for (j, &b) in tail.iter().enumerate() {
        if b >= 0xC0 {
            push(base + j as u32, b);
        }
    }
    wide
}

impl<'s> LineStarts<'s> {
    /// The table of `source`, in one pass over its bytes, and a second over
    /// a source that is not all ASCII.
    ///
    /// # Panics
    ///
    /// If `source` is 4 GiB or longer.
    pub fn new(source: &'s str) -> Self {
        assert!(
            u32::try_from(source.len()).is_ok(),
            "a source is shorter than 4 GiB"
        );
        let first = if source.starts_with('\u{FEFF}') {
            '\u{FEFF}'.len_utf8() as u32
        } else {
            0
        };
        let mut starts = vec![first];
        // A chunk's `\n`s as a bit mask, which the compiler vectorises, then
        // one push per set bit: most chunks hold no `\n`, and those cost a
        // compare of the whole chunk. In range: every index is below the
        // source's length.
        const CHUNK: usize = 32;
        let (chunks, tail) = source.as_bytes().as_chunks::<CHUNK>();
        let mut base = 0u32;
        for chunk in chunks {
            let mut mask = 0u32;
            for (j, &b) in chunk.iter().enumerate() {
                mask |= u32::from(b == b'\n') << j;
            }
            while mask != 0 {
                starts.push(base + mask.trailing_zeros() + 1);
                mask &= mask - 1;
            }
            base += CHUNK as u32;
        }
        for (j, &b) in tail.iter().enumerate() {
            if b == b'\n' {
                starts.push(base + j as u32 + 1);
            }
        }
        let wide = if source.is_ascii() {
            Vec::new()
        } else {
            wide_chars(source.as_bytes())
        };
        LineStarts {
            source,
            starts,
            wide,
        }
    }

    /// How many lines the source has: one more than its `\n`s.
    pub fn line_count(&self) -> usize {
        self.starts.len()
    }

    /// The first byte of the 1-based `line`.
    ///
    /// # Panics
    ///
    /// If the source has no line `line`.
    pub fn line_start(&self, line: u32) -> usize {
        match (line as usize)
            .checked_sub(1)
            .and_then(|i| self.starts.get(i))
        {
            Some(&start) => start as usize,
            None => panic!("a {}-line source has no line {line}", self.starts.len()),
        }
    }

    /// The byte offset of `pos`: its line's start, plus its column, plus the
    /// excess (see [`Self::wide`]) of the non-ASCII characters between. Each
    /// such character found before the offset moves it on by its excess, so
    /// this costs a search for the line's first one and a step per one
    /// before the offset, and an ASCII line no step at all. A column in line 1
    /// of a source with a file-start BOM counts from past the BOM, so offset
    /// 0, which [`LineCursor::advance_to`] gives column 0, comes back as the
    /// BOM's end.
    ///
    /// # Panics
    ///
    /// If the source has no line `pos.line`, or if `pos.col` ends inside a
    /// surrogate pair or past the line's end.
    pub fn byte_offset(&self, pos: LinePos) -> usize {
        let start = self.line_start(pos.line);
        let line_end = self
            .starts
            .get(pos.line as usize)
            .map_or(self.source.len(), |&next| next as usize - 1);
        let mut wide = self.wide.partition_point(|&(at, _)| (at as usize) < start);
        let base = wide.checked_sub(1).map_or(0, |i| self.wide[i].1);
        let mut offset = start + pos.col as usize;
        while let Some(&(at, excess)) = self.wide.get(wide)
            && (at as usize) < offset
        {
            offset = start + pos.col as usize + (excess - base) as usize;
            wide += 1;
        }
        assert!(offset <= line_end, "{pos:?} is past the end of its line");
        assert!(
            self.source.is_char_boundary(offset),
            "{pos:?} ends inside a surrogate pair"
        );
        offset
    }

    /// A cursor at the start of the source.
    pub fn cursor(&self) -> LineCursor<'_> {
        // Line 1 starts past a file-start BOM, whose excess is then the only
        // one before it.
        let line_excess = match self.wide.first() {
            Some(&(at, excess)) if at < self.starts[0] => excess,
            _ => 0,
        };
        LineCursor {
            table: self,
            line: 0,
            last: 0,
            wide: 0,
            excess: 0,
            line_excess,
        }
    }
}

/// A position in a [`LineStarts`] that only moves forward, so finding the
/// line and column of each of an ascending run of offsets costs one step per
/// line and per non-ASCII character crossed, not a search or a rescan.
#[derive(Debug, Clone)]
pub struct LineCursor<'a> {
    table: &'a LineStarts<'a>,
    /// The 0-based index of the line holding `last`.
    line: usize,
    /// The offset of the last [`Self::advance_to`].
    last: u32,
    /// How many non-ASCII characters start before `last`.
    wide: usize,
    /// The excess (see [`LineStarts::wide`]) of those characters.
    excess: u32,
    /// The excess of the non-ASCII characters before `line`'s start.
    line_excess: u32,
}

impl<'a> LineCursor<'a> {
    /// Move to byte `offset` and return its line and column. The column
    /// counts UTF-16 code units from the line's start, so it is 0 at the
    /// start of a source with a file-start BOM as well as past it.
    ///
    /// # Panics
    ///
    /// If `offset` is before the cursor's last offset or past the end of the
    /// source, and, with debug assertions on, if it is inside a character
    /// (the filter calls this on every token boundary, where the check would
    /// cost more than the rest of the call).
    pub fn advance_to(&mut self, offset: usize) -> LinePos {
        let source = self.table.source;
        assert!(
            offset <= source.len(),
            "byte {offset} is past the end of a {}-byte source",
            source.len()
        );
        debug_assert!(
            source.is_char_boundary(offset),
            "byte {offset} is inside a character"
        );
        // In range: checked above.
        let offset = offset as u32;
        assert!(
            offset >= self.last,
            "the cursor only moves forward: byte {offset} after byte {}",
            self.last
        );
        let starts = &self.table.starts;
        while starts
            .get(self.line + 1)
            .is_some_and(|&next| next <= offset)
        {
            self.line += 1;
            self.cross_wide(starts[self.line]);
            self.line_excess = self.excess;
        }
        self.cross_wide(offset);
        self.last = offset;
        // Only line 1 of a source with a file-start BOM starts past an
        // offset the cursor can reach (offset 0), whose column is 0.
        let start = starts[self.line];
        let col = if offset <= start {
            0
        } else {
            offset - start - (self.excess - self.line_excess)
        };
        LinePos {
            // In range: there are at most one more lines than the source has
            // bytes.
            line: self.line as u32 + 1,
            col,
        }
    }

    /// Count the non-ASCII characters that start before `offset` into
    /// `wide` and `excess`.
    fn cross_wide(&mut self, offset: u32) {
        while let Some(&(at, excess)) = self.table.wide.get(self.wide)
            && at < offset
        {
            self.excess = excess;
            self.wide += 1;
        }
    }

    /// The table the cursor walks.
    pub fn table(&self) -> &'a LineStarts<'a> {
        self.table
    }
}
