//! The names of the spans [`crate::resolve_file`] opens under the
//! `fold-counts` feature, one around each file and one around each of its
//! phases, so a harness can count the work each phase does
//! (`docs/resolve-what-a-request-reads-plan.md`, Stage 0).
//!
//! The spans are `trace`-level and carry no data but the file's size. They
//! nest only inside [`FILE_SPAN`]: no phase span opens inside another, so a
//! file's cost is its phases' sum plus the work between them. The names exist
//! whether or not the feature is on, so a harness can name them
//! unconditionally; without the feature, nothing opens them.

/// The span around one call of [`crate::resolve_file`]. Its `bytes` field is
/// the file's length in bytes.
pub const FILE_SPAN: &str = "fold_counts.file";

/// The span around `Prescan::of`: the walks over the whole file that run
/// before the declaration walk.
pub const PRESCAN_SPAN: &str = "fold_counts.prescan";

/// The span around a top-level block's seed of the implicitly opened
/// namespaces (FSharp.Core's auto-open modules and their union cases).
pub const IMPLICIT_SEED_SPAN: &str = "fold_counts.implicit_seed";

/// The span around a top-level block's re-entry of what earlier blocks of the
/// same file contributed.
pub const EARLIER_BLOCKS_SPAN: &str = "fold_counts.earlier_blocks";

/// The span around a top-level block's re-entry of what earlier files
/// contributed: the root scope, and the block's own enclosing namespace.
pub const BLOCK_START_SPAN: &str = "fold_counts.block_start";

/// The span around a top-level block's declarations.
pub const DECLARATIONS_SPAN: &str = "fold_counts.declarations";

/// Every phase span, in the order a file opens them.
pub const PHASE_SPANS: [&str; 5] = [
    PRESCAN_SPAN,
    IMPLICIT_SEED_SPAN,
    EARLIER_BLOCKS_SPAN,
    BLOCK_START_SPAN,
    DECLARATIONS_SPAN,
];

#[cfg(all(test, feature = "fold-counts"))]
mod tests {
    use super::*;
    use crate::recovery::SyntaxRecovery;
    use crate::{AssemblyEnv, ProjectItems, resolve_file};
    use borzoi_cst::parser::parse;
    use borzoi_cst::syntax::{AstNode, ImplFile};
    use std::sync::{Arc, Mutex};
    use tracing::span::{Attributes, Id, Record};
    use tracing::{Event, Metadata, Subscriber};

    /// What a [`Recorder`] saw: each fold span's name as it was entered, with
    /// the fold spans open around it, and each `bytes` field.
    #[derive(Default)]
    struct Seen {
        names: Vec<&'static str>,
        open: Vec<Id>,
        entered: Vec<(&'static str, Vec<&'static str>)>,
        bytes: Vec<u64>,
    }

    /// A subscriber interested in the fold spans alone, each given an id of
    /// its own.
    #[derive(Clone, Default)]
    struct Recorder(Arc<Mutex<Seen>>);

    struct Bytes(Option<u64>);

    impl tracing::field::Visit for Bytes {
        fn record_u64(&mut self, field: &tracing::field::Field, value: u64) {
            if field.name() == "bytes" {
                self.0 = Some(value);
            }
        }
        fn record_debug(&mut self, _: &tracing::field::Field, _: &dyn std::fmt::Debug) {}
    }

    impl Subscriber for Recorder {
        fn enabled(&self, metadata: &Metadata<'_>) -> bool {
            metadata.is_span()
                && (metadata.name() == FILE_SPAN || PHASE_SPANS.contains(&metadata.name()))
        }
        fn new_span(&self, span: &Attributes<'_>) -> Id {
            let mut seen = self.0.lock().unwrap();
            if span.metadata().name() == FILE_SPAN {
                let mut bytes = Bytes(None);
                span.record(&mut bytes);
                seen.bytes
                    .push(bytes.0.expect("a file span carries `bytes`"));
            }
            seen.names.push(span.metadata().name());
            Id::from_u64(seen.names.len() as u64)
        }
        fn record(&self, _: &Id, _: &Record<'_>) {}
        fn record_follows_from(&self, _: &Id, _: &Id) {}
        fn event(&self, _: &Event<'_>) {}
        fn enter(&self, id: &Id) {
            let mut seen = self.0.lock().unwrap();
            let name = seen.names[id.into_u64() as usize - 1];
            let around = seen
                .open
                .iter()
                .map(|open| seen.names[open.into_u64() as usize - 1])
                .collect();
            seen.entered.push((name, around));
            seen.open.push(id.clone());
        }
        fn exit(&self, id: &Id) {
            let mut seen = self.0.lock().unwrap();
            assert_eq!(seen.open.pop().as_ref(), Some(id), "spans exit in order");
        }
    }

    /// The test binary's global subscriber: enables nothing, and leaves every
    /// callsite to be asked per span.
    struct Abstain;

    impl Subscriber for Abstain {
        fn register_callsite(
            &self,
            _: &'static Metadata<'static>,
        ) -> tracing::subscriber::Interest {
            tracing::subscriber::Interest::sometimes()
        }
        fn max_level_hint(&self) -> Option<tracing::level_filters::LevelFilter> {
            Some(tracing::level_filters::LevelFilter::TRACE)
        }
        fn enabled(&self, _: &Metadata<'_>) -> bool {
            false
        }
        fn new_span(&self, _: &Attributes<'_>) -> Id {
            Id::from_u64(1)
        }
        fn record(&self, _: &Id, _: &Record<'_>) {}
        fn record_follows_from(&self, _: &Id, _: &Id) {}
        fn event(&self, _: &Event<'_>) {}
        fn enter(&self, _: &Id) {}
        fn exit(&self, _: &Id) {}
    }

    /// `edit_counts` takes a file's cost as its phases' sum plus the rest, so
    /// every phase span must open directly inside the file's span, never
    /// inside another phase; and each block must open its four.
    #[test]
    fn phases_tile_each_file_without_nesting() {
        let src =
            "namespace A\nmodule M =\n    let x = 1\nnamespace B\nmodule N =\n    let y = A.M.x\n";
        let parsed = parse(src);
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let recovery = SyntaxRecovery::of(&parsed);
        let file = ImplFile::cast(parsed.root).expect("an implementation file");
        let recorder = Recorder::default();
        // A callsite's first use registers it, from whatever thread hits it,
        // with an interest computed from the dispatchers live at that moment:
        // another test resolving first leaves it `never` for this scope too.
        // A global subscriber that answers every callsite `sometimes` leaves
        // each span to ask the thread's own subscriber.
        static ABSTAIN: std::sync::Once = std::sync::Once::new();
        ABSTAIN.call_once(|| {
            tracing::subscriber::set_global_default(Abstain)
                .expect("no global subscriber is installed in the test binary");
        });
        tracing::subscriber::with_default(recorder.clone(), || {
            tracing::callsite::rebuild_interest_cache();
            resolve_file(
                &file,
                &ProjectItems::default(),
                &AssemblyEnv::default(),
                &recovery,
            )
        });
        let seen = recorder.0.lock().unwrap();
        assert!(seen.open.is_empty(), "every span closed");
        assert_eq!(seen.bytes, [src.len() as u64]);
        let block = [
            IMPLICIT_SEED_SPAN,
            EARLIER_BLOCKS_SPAN,
            BLOCK_START_SPAN,
            DECLARATIONS_SPAN,
        ];
        let expected: Vec<(&str, Vec<&str>)> = std::iter::once((FILE_SPAN, vec![]))
            .chain(
                std::iter::once(PRESCAN_SPAN)
                    .chain(block)
                    .chain(block)
                    .map(|phase| (phase, vec![FILE_SPAN])),
            )
            .collect();
        assert_eq!(seen.entered, expected);
    }
}
