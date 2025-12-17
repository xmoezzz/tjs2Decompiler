// SPDX-License-Identifier: MIT
//
// A lightweight heuristic scanner for raw-word regions.
//
// This is not a real bytecode parser. It is useful when you do not yet know the container format.
// It slides a window over little-endian i32 words and ranks offsets by "small integer density".

use byteorder::{ByteOrder, LittleEndian};

#[derive(Debug, Clone)]
pub struct Candidate {
    pub word_offset: usize, // 4-byte words
    pub score: f64,
}

pub fn scan_candidates(data: &[u8], topk: usize) -> Vec<Candidate> {
    if data.len() < 4096 {
        return vec![];
    }

    let window_words = 1024usize; // 4 KiB window
    let step_words = 256usize;    // 1 KiB step
    let max_words = data.len() / 4;

    let mut best: Vec<Candidate> = Vec::new();

    let mut off = 0usize;
    while off + window_words <= max_words {
        let base = off * 4;
        let mut small = 0usize;
        let mut zeros = 0usize;

        for i in 0..window_words {
            let idx = base + i * 4;
            let v = LittleEndian::read_i32(&data[idx..idx + 4]);

            if v == 0 {
                zeros += 1;
            }
            if (0..=0x2000).contains(&v) {
                small += 1;
            }
        }

        let small_ratio = small as f64 / window_words as f64;
        let zero_ratio = zeros as f64 / window_words as f64;

        let score = small_ratio * (1.0 - (zero_ratio - 0.05).abs().min(0.3));

        if best.len() < topk {
            best.push(Candidate { word_offset: off, score });
            best.sort_by(|a, b| b.score.partial_cmp(&a.score).unwrap());
        } else if score > best.last().unwrap().score {
            best.pop();
            best.push(Candidate { word_offset: off, score });
            best.sort_by(|a, b| b.score.partial_cmp(&a.score).unwrap());
        }

        off += step_words;
    }

    best
}
