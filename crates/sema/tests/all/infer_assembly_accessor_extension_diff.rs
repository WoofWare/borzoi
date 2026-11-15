//! A C#-style extension in a referenced assembly may be a property's
//! accessor: F# lets `[<Extension>]` sit on a static property's getter, and
//! FCS then calls `get_Z` as an extension method of the getter's first
//! parameter's type. The assembly reader projects the property, not its
//! accessor method, so the extension gate must read a property of an
//! extension container as the accessors it compiles to.
//!
//! In the fixture (`tests/fixtures/ext_universe_env`):
//!
//! ```fsharp
//! namespace ExtUniverse.Acc
//! type Receiver() =
//!     member _.get_Z(o: obj) = true
//! [<Extension>]
//! type AccExts =
//!     static member Z
//!         with [<Extension>] get (r: Receiver, i: int) = 0L
//! ```
//!
//! With the namespace in scope (opened, or enclosing the calling file), FCS
//! binds `(asR x).get_Z(1)` to the extension getter (`int64`) over the
//! intrinsic `get_Z(obj)` (`bool`), so inference must not commit the
//! intrinsic.

use crate::common::ext_scope::{Call, check};

const CALL: Call = Call {
    binder: "c1",
    text: "(asR x).get_Z(1)",
};

fn source(enclosing: bool) -> String {
    let body = [
        "let asR (r: ExtUniverse.Acc.Receiver) = r".to_string(),
        format!("let {} x = {}", CALL.binder, CALL.text),
    ];
    if enclosing {
        format!(
            "namespace ExtUniverse.Acc\nmodule Use =\n    {}\n    {}\n",
            body[0], body[1]
        )
    } else {
        format!(
            "module Use\n{}\nopen ExtUniverse.Acc\n{}\n",
            body[0], body[1]
        )
    }
}

#[test]
fn an_extension_getter_declines_its_accessor_name() {
    let mut failures = Vec::new();
    for enclosing in [false, true] {
        let label = if enclosing { "enclosing" } else { "open" };
        let checked = check(&[("Use.fs", source(enclosing))], &[CALL]);
        failures.extend(
            checked
                .unsound
                .iter()
                .map(|u| format!("{label}: unsound: {u}")),
        );
        let outcome = &checked.calls[0];
        if outcome.fcs.as_deref() != Some("System.Int64") {
            failures.push(format!(
                "{label}: FCS types the call {:?}, not the extension getter's `System.Int64`",
                outcome.fcs
            ));
        }
        if outcome.ours.is_some() || !outcome.gated() {
            failures.push(format!(
                "{label}: the call should carry ExtensionInScope; ours {:?}, census {:?}",
                outcome.ours, outcome.census
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
