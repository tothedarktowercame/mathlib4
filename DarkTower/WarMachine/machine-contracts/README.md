# Machine-family transcription contracts (packet A, 2026-09-12)

Scope: **model transcription only**, not runtime certification or a readiness-rung
promotion. Registration date `2026-09-12` is the registration of these entries;
it is not a new proof date or a copied Holes helper date. `closed` retains the
transcription disposition; `holder` and bundle scope state the boundary.

`../MachineContracts.lean` is a leaf importing eight machine modules. Its eight
fully qualified constant names use Lean checked quotations. Each signature is a
`checked-reference:` to that elaborated constant, not a guessed type string.
The inherited ten-field Declaration format is retained, with a mechanically
added per-entry `source` object carrying module, commit and content SHA-256.
`MachineDepth.machineDepth` is deliberately a carrier alias, not a numeric depth.

Artifacts:

- `machine-contracts.json`: eight independently identified module contracts.
- `manifest.json`: complete expected nine-module population, including the
  existing `Holes` component; contract byte hash; owner-module, emitter, driver,
  verification-script, shared-emitter and toolchain source pins.
- `wrong-declaration-refusal.txt`: deliberately nonexistent constant fails Lean
  elaboration, exit 1; the exact test source is included.
- `stale-sha-refusal.txt`: disposable manifest changes only the emitter's source
  SHA to zeros; verifier rejects it, exit 1.
- `verification.txt`: unchanged canonical artifacts accepted after that control.
- `build-initial.txt`: successful targeted leaf build before the whitespace-only
  follow-up; `emission.txt`: final emission succeeded, including its mandatory
  targeted build and before/after source verification.

From the mathlib4 root:

```sh
python3 scripts/emit-machine-contracts.py verify DarkTower/WarMachine/machine-contracts/manifest.json
python3 scripts/emit-machine-contracts.py emit /tmp/a-new-machine-contract-output
```

Emission requires tracked source bytes equal both their pinned owning commit and
HEAD. It builds the leaf and invokes a separate `#eval` driver because imported
Holes already defines global `main`. The driver emits **one strict JSON value**;
there is no last-line selection. Duplicate JSON keys, stale/dirty source,
missing or ambiguous populations, missing metadata and unresolved entry pointers
refuse. Existing differing artifacts cannot be overwritten. SHA-256 pins the
bundle bytes in a separate manifest; the manifest is versioned by its git commit
(no circular claim that the manifest hashes itself). Output verification does
not rerun Lean; it checks the frozen source/artifact identity. The two refusal
controls test declaration resolution and stale-manifest rejection respectively.

Holes.lean remained byte-identical:
`4dc0a76b9999d09b2ab49c932117e5b7dcfec523e5e61735b3a84191229cd02b`.
Its existing JSON remained byte-identical:
`333b31739f984d2a291da1ce0551ae219fcc1aa5fb4af4e5a414910b8f69bde9`.
Neither its registry nor the existing emit-contract.sh was changed.

The external Clojure/witness/log pointers are resolved as file:line metadata;
this packet does not revalidate historical readback results or establish runtime
correspondence. Consumers must retain this boundary when using the contracts.
Packet B must implement the checked module union; packet C controls presentation.
No dossier generator, equation registry, control-stage registry or paper output
was edited/regenerated. The R3a equation-host proposal remains unapplied and
requires the requested **Box 2 before/after edge-classification impact assessment
and TN-9a second read**, not just the presence of its eighth contract entry.
