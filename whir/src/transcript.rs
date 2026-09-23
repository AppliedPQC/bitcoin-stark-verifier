//! The verifier's transcript, emitted as script by the reference transcript.
//!
//! [`crate::reference::transcript`] is the schedule Plonky3's verifier executes,
//! written over a two-method [`Sponge`]. [`Emitter`] is a `Sponge` that emits
//! script: driving the reference transcript through it produces, in one pass,
//! the script that runs that transcript on the sponge state and the values it
//! must draw. The transcript logic lives in one place; this module only turns
//! each primitive into stack operations.
//!
//! # The buffering rule, at generation time
//!
//! Plonky3's `DuplexChallenger` buffers observed elements and permutes when
//! eight are pending or when a sample finds pending input or an empty output
//! buffer; samples then pop the rate from the end. None of that needs runtime
//! bookkeeping in script: the schedule is fixed once the proof's shape is, so
//! the emitter keeps the two buffer counts itself and emits [`sponge::absorb`]
//! exactly where the reference sponge would duplex, and reads exactly the rate
//! slot the reference would pop. The lockstep [`reference::Challenger`] is
//! what makes that claim checkable, value by value.
//!
//! # Stack
//!
//! The sixteen-element state sits on top of the main stack, with the pending
//! inputs (at most seven) above it between an observe and the duplex that
//! consumes them. Observed values arrive from the altstack, one
//! `OP_FROMALTSTACK` each, so the caller pushes the transcript's inputs there
//! in consumption order. In [`Mode::Check`] every sample is compared with the
//! value the reference drew, also taken from the altstack, and the state is
//! left as the reference leaves it; [`stream`](Emitter::stream) is the whole
//! altstack, inputs and expected draws interleaved in the order they are read.

use crate::challenger;
use crate::reference::{self, Challenges, Sponge, TranscriptConfig, TranscriptData};
use crate::sponge::{self, RATE};
use crate::treepp::*;

/// What a sample leaves behind.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// Compare the sampled slot with the reference's draw from the altstack
    /// and drop it. The script fails at the first challenge that differs.
    Check,
}

/// A `Sponge` that emits script and tracks the reference sponge in lockstep.
pub struct Emitter {
    reference: reference::Challenger,
    /// Observed elements not yet absorbed, at most `RATE - 1` between ops.
    pending: usize,
    /// Rate slots of the last permutation still unread, popped from the end.
    available: usize,
    mode: Mode,
    parts: Vec<Script>,
    /// Everything read from the altstack, in consumption order.
    pub stream: Vec<u32>,
    /// Permutations emitted.
    pub permutations: usize,
}

impl Emitter {
    pub fn new(mode: Mode) -> Self {
        Self {
            reference: reference::Challenger::new(),
            pending: 0,
            available: 0,
            mode,
            parts: Vec::new(),
            stream: Vec::new(),
            permutations: 0,
        }
    }

    /// `duplexing` over the pending inputs: `absorb(k)`, a squeeze for none.
    fn duplex(&mut self) {
        self.parts.push(sponge::absorb(self.pending));
        self.permutations += 1;
        self.pending = 0;
        self.available = RATE;
    }

    /// The emitted script.
    pub fn script(&self) -> Script {
        let parts = &self.parts;
        script! { for p in parts { { p.clone() } } }
    }

    /// The reference sponge's state, which the script's state must equal.
    pub fn state(&self) -> [u32; 16] {
        self.reference.state()
    }
}

impl Sponge for Emitter {
    /// `DuplexChallenger::observe`: buffer, and duplex at a full rate.
    fn observe(&mut self, value: u32) {
        self.reference.observe(value);
        self.stream.push(value);
        self.parts.push(script! { OP_FROMALTSTACK });
        self.available = 0;
        self.pending += 1;
        if self.pending == RATE {
            self.duplex();
        }
    }

    /// `DuplexChallenger::sample`: duplex if anything is pending or nothing is
    /// left to read, then take the highest unread rate slot.
    fn sample(&mut self) -> u32 {
        let value = self.reference.sample();
        if self.pending > 0 || self.available == 0 {
            self.duplex();
        }
        self.available -= 1;
        let slot = self.available;
        match self.mode {
            Mode::Check => {
                self.stream.push(value);
                self.parts.push(script! {
                    { challenger::sample(slot) }
                    OP_FROMALTSTACK
                    OP_EQUALVERIFY
                });
            }
        }
        value
    }
}

/// The transcript as script, with what it draws and the stream it consumes.
///
/// Stack in: the sixteen-element initial state (all zero for a fresh
/// challenger) with the [`Emitter::stream`] on the altstack, first element on
/// top. Stack out: the state the reference sponge ends in.
pub fn transcript(cfg: &TranscriptConfig, data: &TranscriptData, mode: Mode) -> (Emitter, Challenges) {
    let mut emitter = Emitter::new(mode);
    let challenges = reference::transcript(cfg, data, &mut emitter);
    (emitter, challenges)
}
