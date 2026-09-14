# Palomar readiness tracker

Status: PREPARATION. Contract and Apache-2.0 approved. Public GitHub visibility was explicitly approved and verified PUBLIC on 2026-09-13. A verified release and Palomar submission remain pending.
Research theorem scope: eight of eight paper deliveries formally closed.
Release selected surface: six declarations, corresponding to A/B/C/A1/A2.

| Stage | Status | Remaining exit test |
|---|---|---|
| P1 source freeze/licence | DONE | Per-file source/release hashes saved; original files unchanged |
| P2 Challenge/Solution | IDENTITY PASSED | Interface6 reached NanoDa after all six target/dependency comparisons; full replay still required |
| P3 extraction/build | SERIAL PASSED / COLD FAILED | Linux 976/976 passed; latest cold default build OOM at 6 GiB |
| P4 independent verification | STANDALONE NANODA PASSED | Combined Comparator+NanoDa and exact pipeline replay still required |
| P5 metadata/rehearsal | TODO | Current schemas, assessability, current preflight/full replay |
| P6 public handoff | TODO | Exact immutable checked commit, explicit push approval, manual intake |

Approved limits:1000 local Lean modules,125000 lines,800 Challenge lines,
six selected theorems,zero source-import-unreachable release modules.
Current extracted proof modules973/119379 original lines; licence headers add
962 lines. Challenge269 lines; Solution is a six-theorem exact wrapper.
Recount after every interface change; these are import counts, not a claim of
kernel-minimal proof terms.

Local .lake/packages is an ignored dependency-cache link to the pinned source
cache. It is not part of the release, a proof-source dependency, or a clean
Linux replay. No external state has changed.

## Readiness iteration R1 — 2026-09-13

- Source extraction passed with hashes for all973 modules and header-only
  Apache licence conversion; original proof files untouched.
- Standalone `lake build Challenge` session69160 exit0/1192jobs, Challenge14s;
  exactly six deliberate theorem holes, no extra helper holes.
- `Solution.lean` checked in the research environment (session49647's second
  command exited0); this is preliminary, not extracted-build evidence.
- Extracted `lake build Solution` is running in session48962; output at
  `/tmp/gallai-release-solution.log`. Re-poll this handle, do not restart merely
  because output is quiet. It rebuilds licensed source modules, not proofs
  imported from the source laboratory.
- Strict source-cone audit exit0:975 local modules/120696lines;
  Challenge1module/269lines;Solution974modules/120427lines;unreachable0.
  Licence,6/6 theorem docstrings and nine package pins passed. Warnings:
  uncommitted snapshot and final source-commit/provenance reconciliation.
- Exact exporter gate PASS: Lean4.33.0; exporter15f6055e299ad5b89345e533cc2192f4cc00f659.
- Trusted dependency provenance PASS: Mathlibdb584cd6d46c92f209a44c0f1c829460d327499d
  is an ancestor of the canonical master branch. Both gates used public
  Palomar policyef2fa1eadcb246c2346ddba39b52eaa53d4bb763.
- Current Palomar `load_formalization_metadata` validation PASS with PyYAML6.0.3.
  This is the metadata minimum only, not complete prepare/full verification.
- Linux replay environment unavailable: colima reports missing Lima; no Docker,
  Podman or Orb command found. No VM software was installed or started.
- No commit, remote, push or live submission. The package is NOT READY yet.

Remaining named obligations: standalone Solution build; Comparator and NanoDa;
complete current prepare/full replay; final independent statement/readability
review; immutable source/release checkpoint and authorized public handoff.

## Public repository and resumed release build — 2026-09-13

- User approved public visibility, a release tag, and Palomar submission preparation.
- GitHub `shaikidris/gallai-bowtie-removal` was changed from PRIVATE to PUBLIC
  and verified through the GitHub API. No release tag or registry submission
  was created by that visibility change.
- No standalone `Solution.olean` was present when the release was resumed.
  `lake build Challenge Solution` was started in execution session 9904;
  a completion result must be recorded before treating this gate as passed.
- Comparator/NanoDa and current preflight/full replay remain pending.
- Live Palomar intake is a user handoff, not an agent-driven submission.

## Failure diagnosis and clean serial replay — 2026-09-13

- Public Palomar run 34746442120 terminated its Python executor with SIGKILL
  (exit 137), after about 42 minutes. No mechanical report was uploaded.
  Memory pressure is suspected, not established by runner telemetry.
- Local aggregate session 9904 exited 1, with multiple certificate-module
  failures. This supersedes the earlier live-build status.
- Unchanged `Gallai.Certificates.SizeTwoCoverage.Block09` passed alone in
  session 8021 (exit 0; compiler 92s, wall 106.16s). A process sample showed
  about 3.3 GB resident memory. This rules out a deterministic proof error
  in that block, not in every failed module.
- A diagnostic runner under `../submission-preparation/serial_release_build.py`
  orders all 975 local modules by imports, builds one at a time, stops on
  the first failure, and finally builds Challenge/Solution together.
- Clean replay evidence is under
  `../submission-preparation/clean-serial-2026-09-13/`. Previous local build
  outputs were preserved there, not deleted. Dependency caches are reused;
  this is a clean local-source build, not a clean Linux independent replay.
- No theorem, proof implementation, dependency pin, or trust policy changed.
  Clean serial local replay subsequently PASSED all 976 steps (975 modules
  plus the combined roots), with zero failures and 9491.89 seconds summed
  step time. A fresh `lake --no-build build Challenge Solution` also exited 0.
  A Palomar-compatible resource repair remains unvalidated.

## Corrected rehearsal inputs and full replay — 2026-09-13

- Earlier personal-fork preflights failed on omitted dispatch inputs, not
  Lean proof checking. Both required fields are now explicitly supplied.
- Preflight 34769305518 succeeded: report stage `prepared`, status `pending`
  (expected for preflight), empty errors, source f7e59175cb3d5fd77ecf186556ab326d61ab7a0d.
- Inputs and report are retained under `../submission-preparation/`.
- Full personal-fork rehearsal:
  https://github.com/shaikidris/PalomarSubmission/actions/runs/34769385422
- This uses unmodified verifier ef2fa1eadcb246c2346ddba39b52eaa53d4bb763.
  It is an exact baseline replay, NOT a validated resource-safe modification.
  Comparator/NanoDa success must come from its final mechanical report.
  It creates no live Palomar submission or registration.

## Private checkpoint and cross-record preparation — 2026-09-13

Historical section below predates publication and is not the current visibility
or build status. See the Linux replay update at the end of this file.

The private release repository is `shaikidris/gallai-bowtie-removal`, verified
PRIVATE through GitHub. This checkpoint is not a completed verification release.
The live build remains the R1 process; no restart was requested.
Zenodo software, SSRN preprint, and Palomar metadata are being prepared locally.
No DOI, SSRN identifier, or Palomar registration exists in this preparation.
See `SUBMISSION_LINKS.md` for the reciprocal-link sequence. Private GitHub
availability does not satisfy Palomar's public immutable-source requirement.

## Local Linux replay — 2026-09-13

- Full fork run 34769385422 failed with exit 143. No mechanical report or
  internal stage logs were uploaded; the precise termination cause remains
  unconfirmed. Do not equate this with the earlier exit-137 failure.
- The separate `gallai` Colima/Lima guest runs Ubuntu 24.04 ARM64, 4 CPUs,
  8 GiB RAM. This differs from the GitHub x86-64 runner. Initial cloud-final
  provisioning failed because `rsync` was unavailable in the package index.
  A successful apt index refresh and prerequisite installation repaired that
  package issue; the overall Colima provisioning status is not yet revalidated.
- Guest SSH, GitHub DNS resolution and a sudo systemd-run smoke test passed.
- Pinned Comparator 575674928e239f5bc452aab72d1dd7b0f1326494 built (16 jobs).
  Pinned lean4export 15f6055e299ad5b89345e533cc2192f4cc00f659 built (6 jobs),
  using the exact submitted Lean v4.33.0. Comparator uses its own declared
  v4.34.0-rc1 toolchain, as in the upstream workflow.
- Pinned NanoDa 68d5ca9db226849b41a6fff59d796ff19d0a8840 built with the
  unchanged lockfile. Ubuntu Cargo 1.75 could not read lockfile version 4;
  Rust 1.98.1 installed via checksum-checked rustup 1.28.2 resolved this.
- These are TOOL BUILD results, not successful theorem verification.
- Exact source f7e59175cb3d5fd77ecf186556ab326d61ab7a0d was transferred by
  local Git archive/bundle; a guest git diff check passed before the build.
  No credentials or Mac build outputs were transferred.
- Clean Linux serial source build started under `gallai-linux-source-build`.
  It uses LEAN_NUM_THREADS=1, MemoryHigh=5G and MemoryMax=6G. Initial observed
  stage: 1/976, fetching pinned Mathlib. Completion remains PENDING.
- Guest source and per-module evidence:
  `/home/lima.guest/research/gallai-two-exception/source/linux-serial-evidence/`.
  The source directory is bind-mounted to the guest's 30 GiB data disk; this
  manual mount is not yet configured to persist across a VM restart.
- Inspect live output using `LIMA_HOME=/Users/shaik.i/.colima/_lima limactl
  shell --workdir / colima-gallai -- journalctl -u gallai-linux-source-build
  --no-pager -n 30`. Per-module logs and progress.jsonl retain build evidence.
- Remaining gates: completed clean Linux build, selected-declaration
  Comparator/NanoDa checks, then full confined Palomar replay. No new push,
  live submission or registration was performed by this local replay work.

### Resource repair iteration 1 — 2026-09-13

Baseline: steps 1–538 passed. Step 539, SizeTwoCoverage.Block00, stalled at
the locally imposed 5 GiB soft limit. The worker was observed waiting in
`mem_cgroup_handle_over_high`, with millions of high-limit events. Raising
the soft limit to 6 GiB exposed a confirmed cgroup OOM at the unchanged
6 GiB hard limit. This is local evidence, not proof of the cloud failure cause.

Change class: MAINTENANCE, proof-only. The single 256-case witness proof was
split into 256 private closed-case lemmas and a public assembly theorem in
the same module. Tables, imports, public signatures, licence headers and
axiom policy are unchanged. No new Lean modules or weaker theorem statements.

Measured Block00 results in the ARM64 guest:

| Gate | Result | Wall time | Peak process RSS |
|---|---|---:|---:|
| Optimized Lake build | PASS | 42.72 s | 2,552,236 KiB |
| Selected witness export | PASS | 3.91 s | 2,002,532 KiB |
| NanoDa replay | PASS | 13.39 s | 64,192 KiB |

The 21 MiB export selects `Gallai.Certificate.SizeTwo.Coverage.Block00.witness`
and its dependencies. NanoDa used only propext, Quot.sound and Classical.choice,
with unpermitted axioms treated as errors. These gates do NOT certify the six
submission declarations. Both build and replay ran within a 6 GiB hard cap.
Guest journal units: `gallai-block00-opt1`, `gallai-block00-replay1`.

The same generated proof rewrite is now applied to all 16 size-two blocks in
the research and release trees. The source generator passes its four tests;
its exact 17-file/4,096-witness regeneration check passes. The release's
different licence header was preserved rather than overwritten by the generator.

Full-scope continuation is RUNNING as `gallai-linux-source-build-opt1`, from
step 539, with LEAN_NUM_THREADS=1 and MemoryHigh=MemoryMax=6 GiB. The first
538 cached steps are inherited evidence, not new measurements. Guest logs,
progress and the exact uncommitted source patch are in
`source/linux-serial-opt1-evidence/`. The runner's new `--start-at` option
records skipped modules explicitly; it does not claim a fresh all-module run.

Decision: retain the full submission scope while this repair is tested.
Fallback expansion/sharpness-only submission has NOT been adopted.
Remaining: all modified blocks and downstream roots; complete selected-root
Comparator/NanoDa; resource-faithful confined replay; approved checkpoint/push.

### Resource repair iteration 2 — 2026-09-13

Iteration 1 passed all 16 SizeTwoCoverage blocks and their assembly (step 555).
Step 556, SizeTwoExceptionClassification, hit a confirmed 6 GiB cgroup OOM.
Its nonbasic_profile expanded 234 by 13 cases in one tactic proof.

Bounded sibling scan: the same large row-splitting family occurs in all three
classification theorems, forced_covered, high_representative_covered, and
the accepted theorem in 12 SizeTwoRichCatalogue blocks. These 15 files are
rewritten to private per-row helpers followed by the identical public theorem.
The smaller finite splits in structural modules and existing catalogue
assemblies are unchanged. Zero-syndrome `decide` proofs are a different
implementation pattern and remain a pending build/resource test, not a proved
resource failure.

Transformation and before/after hashes are retained in
`../submission-preparation/split_size_two_case_proofs.py` and
`../submission-preparation/opt2-source-hashes.jsonl`. This is a one-off
post-generation repair, not yet integrated into the original rich generator.
The public-signature/table/import comparison passed for all 15 files, as did
git diff --check. Lean and independent-replay acceptance remain pending for
this second batch. No axioms, native_decide or weaker signatures were added.

RUNNING: `gallai-linux-source-build-opt2`, resumed at 556 with the unchanged
6 GiB hard cap. Evidence: guest `source/linux-serial-opt2-evidence/` (including
source.patch and progress.jsonl). The earlier 555 successful steps are retained.

User preapproved commit and push of the optimization batch ONLY AFTER the
full build and required validation succeed. Nothing has been committed or
pushed on the basis of the focused tests. Full submission scope is unchanged.

Iteration-2 interim results: classification PASSED in 70.17 s;
forced_covered's module PASSED in 28.78 s; the first two rich blocks PASSED
in 5.40 s and 8.21 s. At step 565 the run remained active with a sampled
cgroup peak of 3,213,504,512 bytes (about 2.99 GiB). These are focused build
results, not completion of the remaining roots or independent replay.

### Resource repair iteration 3 — 2026-09-14

Iteration 2 passed through step 582, including all repaired classification,
forced and rich-catalogue proofs. ThreeAnchorCheapOrbits at step 583 hit a
confirmed 6 GiB cgroup OOM at 00:04:54 Dubai time.

Active goal: repeat evidence-based, proof-preserving repairs and resumptions
until the Linux build and complete selected-theorem validation pass. A thread
heartbeat `gallai-build-repair-and-validation` checks every 15 minutes; it
should not restart healthy work and should pause when the goal is complete.

Candidate repair: replace cheap_coverage's single 1,024-state decide with
32 separately checked 32-state chunks and a quotient/remainder assembly.
The original coverage statement, code list, and individual reconstruction
certificates remain unchanged. Whether this removes the full module's peak
is still under test; the previous OOM did not identify a declaration.

Iteration 3 stopped at step 583 with exit 1 after 122.92 s: the new
`fin_cases` assembly lacked its tactic import. This was not an OOM; cgroup
peak was 2,804,203,520 bytes (about 2.61 GiB). The log identifies an unknown
tactic at line 175 and the resulting unclosed assembly goal.

Repair: explicitly import `Mathlib.Tactic.FinCases`, already present in the
pinned dependency tree. No statement, certificate data, or trust change.
Learning: introducing a tactic into a generated module requires checking
its actual imports, not relying on imports of sibling modules.

RUNNING: `gallai-linux-source-build-opt4`, from step 583, MemoryMax=6 GiB.
Evidence: guest `source/linux-serial-opt4-evidence/`; previous failed attempt
preserved under `source/linux-serial-opt3-evidence/`. Goal remains ACTIVE;
full validation and conditional commit/push remain pending.

Iteration-4 result at step 583: ThreeAnchorCheapOrbits PASSED in 138.18 s;
its selection consumer also PASSED in 3.02 s. Sampled run cgroup peak was
2,000,224,256 bytes (about 1.86 GiB), below the unchanged 6 GiB ceiling.
The run subsequently reached step 590. This closes the observed module OOM,
not the full Linux or independent verification gate.

The research generator `formal/scripts/import_three_anchor_orbits.py` now
emits the 32-chunk proof and explicit FinCases import. An exact-text check
confirmed its coverage proof matches the Linux-checked release source.
Full generator/source synchronization remains a release closeout check.

Rich-catalogue synchronization: the research `import_size_two_rich.py` now
emits the 15 private row proofs and unchanged public assembly per block.
All 12 regenerated blocks were compared with the Linux-passed release
source: definitions, proof tokens and imports match, ignoring comments and
whitespace only. The research outputs were regenerated after verifying
their prior content matched the release baseline modulo those same cosmetic
differences; their original research licence headers are retained. The
classification/forced files have now also been synchronized using the bounded
row-proof transformation. Rich coverage's generator now emits all 234 private
row proofs and its unchanged public assembly. Full regeneration of rich
coverage and ThreeAnchorCheapOrbits matched the Linux-passed release code
(comments and whitespace ignored), and both research outputs were updated.
All four updates first verified their research source matched the unoptimized
release baseline, so unexpected existing changes would have stopped the batch.
This synchronization check is not a replacement for the pending full build
and six-selected-theorem independent verification.

Queued next gate: `gallai-replay-handoff-opt4` is a local waiting controller.
It requires the build service's successful terminal result, its SUCCESS marker,
and unchanged source hashes before launching Comparator with all six original
selections and NanoDa enabled. The actual verifier runs in a separate confined
service with no AF_UNIX/network access and the same 6 GiB ceiling; it does not
overlap the build. Streaming logs and tool/source hashes go to guest
`/home/lima.guest/research/gallai-two-exception/selected-replay-opt4-evidence/`.
The task-local script is `submission-preparation/replay_after_build.py`.
This is a pinned diagnostic replay, not the exact full Palomar pipeline or
the final cold CI-shaped build, both of which remain separate readiness gates.

### Linux serial completion and replay — 2026-09-14

At 06:36:43 Dubai, opt4 reached 976/976 and the final combined
`Challenge Solution` build exited zero. The service exited successfully;
its journal reports a 5.1 GiB peak with zero swap. This completes the serial
sequence across the recorded resumptions, using previously passed Linux
artifacts for earlier steps; it is not a fresh all-at-once cold build.

Two handoff-only failures were repaired without changing any Lean source:
systemd unloaded the completed transient unit (the controller now requires
the durable SUCCESS marker and successful final-root progress record), and
sudo's executable lookup could not resolve `lake` (now an explicit path).
The preserved failed handoff directories are `selected-replay-opt4-evidence`
and `selected-replay-opt4b-evidence` in the guest project directory.

FAILED: controller `gallai-replay-handoff-opt4c`, verifier service
`gallai-linux-source-build-opt4-replay`, evidence
`selected-replay-opt4c-evidence`. Comparator's cached Lake build completed
successfully (2226 jobs), then export completed but statement comparison
rejected `Gallai.Palomar.theoremA`: "Challenge and solution theorem statement
do not match". Service runtime 33.089 s, memory peak 1.3 GiB. NanoDa was not
reached. The exact diagnostic is in `selected-replay-opt4c-evidence/replay.log`.
The source-level theorem texts match; the pinned comparator checks exported
constant values and dependency identity, not merely source text or provable
equivalence. Exact elaborated-type diagnosis is the next obligation. Do not
weaken the selected statement or widen the trust policy to bypass this gate.

Interface diagnosis: printed fully explicit types showed only parameter-order
differences in the copied `WholeBowtie.activity` (A and C) and `syndrome` (C).
Challenge now declares their parameters explicitly in proof-library order,
including `activePrivate`, with identical formulas. Its narrow Linux build
passed; all six printed elaborated theorem types then matched exactly.
Replay `selected-replay-interface1-evidence` passed target-type comparison but
found a dependency mismatch in `TwoBowtie.oddVertices`. Explicit definition
printing identified named universe `u` in Challenge versus source-generated
`u_1` in the proof library. The TwoBowtie section is being aligned with the
original `Type*` variable declaration. This is interface-identity maintenance,
not a change to the mathematics; independent replay remains incomplete.

Further dependency-identity repair (interface2–interface5): aligned the
TwoBowtie universe declaration; explicitly reproduced the checked numeral
helpers for `activePrivate` and `syndrome`, including the exact Zero instance
and raw numeral argument. These reproduce compiler-generated names from the
pinned source and therefore need rechecking after refactors. Their proofs use
`Nat.instNeZeroSucc`, not new axioms. Interface5 passed those dependencies and
stopped at `Gallai.exists_pathBudget`, whose Challenge proof is different from
the library proof. Its statement matches, but this comparator requires the
dependency constant itself to match. The next repair must align that proof
and its required supporting definitions; no trust relaxation or removal of
the selected sharpness theorem is authorized. NanoDa remains not reached.

Interface6: Challenge now reproduces the source `exists_pathBudget` proof,
its `exists_singleEdgePath` lemma and `Decomposition.ofFamily` definition.
The narrow rebuild passed and the original six-target Comparator advanced
past statement/dependency identity to "Running nanoda kernel on solution".
RUNNING: `selected-replay-interface6-evidence-worker`, controlled by
`gallai-replay-handoff-interface6`, evidence in the matching guest directory.
NanoDa is now reached but has not yet reported success. The 6 GiB resource
ceiling and permitted three axioms remain unchanged. Existing prior-failure
reports are retained, not overwritten. Cold-build and exact-pipeline replay
remain separate required readiness gates before the preapproved push.

Cold-root preparation: guest `cold-source1` is a separate copy with no
project `.lake/build`; pinned dependency caches are retained. All 979 Lean
source/config files compared byte-for-byte with the current source, with
hashes in `cold-source1-hashes.json`. Default `lake build` selects Challenge
and Solution. The cold build has NOT started while NanoDa remains live.
The replay snapshot helper was corrected to include `lakefile.toml` as well
as optional `lakefile.lean`; the current cold comparison includes the TOML
file explicitly. Earlier replay source-hash inventories omitted that file.
### Independent-kernel resource failure — 2026-09-14

Interface6 passed Comparator identity but failed with confirmed cgroup OOM
after 354.82 s. Kernel evidence at 08:24:04 Dubai identifies NanoDa as the
killed process: approximately 4.94 GiB anonymous RSS, while Comparator retained
about 0.96 GiB anonymous RSS. The combined service hit exactly 6 GiB. Source
hashes remained unchanged. This is NOT independent-kernel success.

Next diagnostic: stream the same six-root export to disk and invoke the
unchanged pinned NanoDa separately under 6 GiB, eliminating Comparator's
retained export strings from the simultaneous footprint. A standalone pass
would isolate overhead; it would not by itself certify the exact Palomar
pipeline. Cold-root build is prepared but not started.

RUNNING: `gallai-streamed-kernel1` performs a disk-backed export of the same
six selected Solution declarations, then invokes the pinned NanoDa alone
with the original three-axiom allowlist and hard error on unpermitted axioms.
The service retains the 6 GiB ceiling. Evidence lives in guest
`streamed-kernel1-evidence`, including source/config/tool hashes, export hash,
timings, and kernel output. The task-local driver is
`submission-preparation/streamed_kernel_replay.py`. No cold build overlaps it.

Guarded next gate: `gallai-cold-root1` is running only its waiting controller.
It requires a successful `streamed-kernel1-evidence/result.json`, unchanged
source hashes, and an absent project build cache before ordinary `lake build`
starts in `cold-source1`. It stops without building if kernel validation
fails. Evidence is `cold-root1-evidence`; dependency caches are retained.
This is not yet an exact Palomar pipeline pass. On the latest live check,
NanoDa had consumed over 15 minutes CPU time and had zero OOM kills.

### Standalone NanoDa pass and cold default build — 2026-09-14

`gallai-streamed-kernel1` finished successfully and was deactivated by systemd.
Durable evidence is `streamed-kernel1-evidence/result.json`:

- `kernel_exit_code`: 0
- `kernel_seconds`: 1670.47 (wall 27:48.57)
- `source_unchanged`: true
- export SHA-256 unchanged:
  `78ef17a76d1a56f5d0a476c16b45d11660b51874146a15c59e23a1145f034ba7`
- six selected Solution roots unchanged
- `/usr/bin/time -v` exit status 0; maximum RSS 5,198,008 KiB (about 5.0 GiB)
- service memory peak 6.0 GiB, swap 0, `oom_kill=0`
- permitted axioms remain `propext`, `Quot.sound`, `Classical.choice`
- `unpermitted_axiom_hard_error`: true
- `official_palomar`: false

This is a **standalone** disk-backed NanoDa pass under a 6 GiB cap. It does
**not** prove the official combined Comparator+NanoDa Palomar pipeline.

`gallai-cold-root1` observed the successful result and started ordinary
`/usr/bin/time -v lake build` in `cold-source1` at 08:55:54 guest time.
That gate is RUNNING. It is a cold **project** default-concurrency build with
retained dependency caches, not a serial per-module replay and not the exact
Palomar pipeline. No commit or push is authorized until this build, the
combined six-theorem Comparator/NanoDa replay, and `verify_submission.py`
succeed.

### Cold default build OOM — 2026-09-14 09:06 Dubai

The preceding RUNNING state is superseded. `gallai-cold-root1` failed at
09:06:20 with Result=oom-kill, 6.0 GiB memory peak and no swap. The final
printed successful job was 1663/1948, SizeTwoCatalogue.Orbit165; this does not
identify the module that failed. Kernel logs show Lake and three concurrent
Lean processes (89092, 89094, 89100). The killed process 89092 had 293552 KiB
anonymous RSS and 998144 KiB file RSS. The unit terminated without a driver
result.json. Failure evidence is in cold-root1-evidence/build.log and the
system/kernel journals. Next: diagnose aggregate default-build memory and
concurrency before another replay. The standalone NanoDa pass remains valid;
no cold-build or exact-pipeline pass, commit, or push is claimed.

Correction: the first OOM victim was lean pid **88342**, anonymous RSS
5,050,360 KiB (~4.82 GiB), total-vm ~14.8 GiB. Three smaller concurrent
Lean jobs (~260–290 MiB anon each) plus Lake pushed the cgroup to the 6 GiB
cap. `ThreeAnchorSyntheticOrbits` had already completed (460 s, 5.2 MiB
olean). `ThreeAnchorOriginalOrbits.olean` was absent; that module is the
same 474-`decide` pattern and is the in-flight fat compile. Preserved
`cold-root1-evidence` was not overwritten.

Proof-only repair: split `ThreeAnchorOriginalOrbits.lean` into 15 block
modules of 32 (last 26) accepted witnesses, same public names and
`OriginalAccepted` types. Parent file is now imports only. Consumer
`ThreeAnchorOriginalSelection` is unchanged. Generator
`import_three_anchor_orbits.py` refuses to emit the old monolith.
RUNNING: `gallai-original-orbits-split1`, MemoryMax=6G, default Lake
concurrency, target
`Gallai.Certificates.ThreeAnchorOriginalOrbits` and
`Gallai.Certificates.ThreeAnchorOriginalSelection`. Evidence:
`original-orbits-split1-evidence`. This is not yet a new cold default
build.

### OriginalOrbits split pass; RetainedOrbits OOM — 2026-09-14

`gallai-original-orbits-split1` succeeded: 15 blocks 8–20 s, parent 1.3 s,
selection 1.7 s, wall 62 s, `/usr/bin/time` max RSS 1,851,476 KiB
(~1.77 GiB) versus 4.82 GiB for the monolith. Exit 0.

`gallai-cold-root2` (resumed default `lake build` in `cold-source1`, not a
true cold tree) then OOM-killed at 09:30:18. Victim lean pid 90006,
anonymous RSS 3,991,180 KiB (~3.81 GiB), compiling
`ThreeAnchorRetainedOrbits`. Last printed jobs were SizeTwoCoverage
blocks 10–15. Evidence: `cold-root2-evidence`.

In-file 32-chunk split of `retained_coverage` (`gallai-retained-orbits-split1`)
failed at assembly: `hn : n ∈ retainedCodes` vs `⟨q*32+r⟩ ∈ retainedCodes`.
Evidence: `retained-orbits-split1-evidence`. Preserved.

Cert-file repair (same pattern as OriginalOrbits / SizeTwoCoverage): Core
plus 32 `BlockNN` modules, each one 32-code `decide`; parent is imports plus
CheapOrbits-style `simpa only [heq] using h`. Public `retained_coverage` /
`state_coverage` / `coreOrder` / `Normalizes` unchanged. No `native_decide`.
`gallai-retained-orbits-split2` under MemoryMax=6G: 937 jobs, wall 40.19 s,
`/usr/bin/time` max RSS 2,232,256 KiB (~2.13 GiB), exit 0. Blocks 1.6–8.5 s,
parent 913 ms. This is not a cold default build and not a Palomar pipeline
pass.

Same cert-file pattern applied to `ThreeAnchorSyntheticOrbits` (next cold
OOM candidate): Core; 32 `PairNN` modules for `pair_partition`; 15 `BlockNN`
modules for the 474 `acceptedN` witnesses; parent is imports plus the public
`pair_partition`. Generator refuses the old monolith.
`gallai-synthetic-orbits-split1` under MemoryMax=6G: 950 jobs, wall 1:10.98,
`/usr/bin/time` max RSS 2,063,908 KiB (~1.97 GiB), systemd 1.8G peak, exit 0.
32 Pair + 15 accept blocks + parent + `ThreeAnchorSyntheticSelection`.
Evidence: `synthetic-orbits-split1-evidence`. Not a cold default build.

True cold default `lake build` (no project `.lake/build`; package caches
kept): `cold-source3` on `/dev/vdb1[/gallai-cold-source3]`, snapshot 1075
files match `source/`. `gallai-cold-root3` OOM-killed at 10:09:27 after
14m13s, MemoryPeak=6.0G, swap 0. Victim lean pid 96607, anon-rss
5,106,736 KiB (~4.87 GiB). In-flight without olean:
`ZeroSyndromeUniverse` (`highInputs_card : highInputs.card = 3047 := by
decide` over `Finset.univ` on `Fin 4 → Fin 8`, 4096 states) plus
SizeTwoCatalogue Orbit161–163. Evidence: `cold-root3-evidence`. Preserved.

Repair: eight first-row fiber `decide`s in `ZeroSyndromeUniverse/Fiber0`–
`Fiber7` (cards 295, 380×6, 472) plus parent sum; public
`highInputs_card` unchanged. No `native_decide`.
`gallai-zero-universe-split1` compiled Core+Fiber0–7 then failed parent
`sum_congr` metavariables (exit 1, not OOM; 5.3G peak).
`gallai-zero-universe-split2` warm rebuild exit 0, wall 5.33 s, RSS
1,970,908 KiB; unused `change` tactic removed. Not a cold default build.

True cold default `lake build` of this source: `cold-source4` on
`/dev/vdb1[/gallai-cold-source4]`, snapshot 1084 files, no project
`.lake/build`. `gallai-cold-root4` OOM-killed 12:20:28 after 10m51s,
MemoryPeak=6.0G. Victim lean pid 107569 (`ThreeAnchorZeroOrbits`,
anon-rss 2,906,236 KiB) plus Fiber2/3/4 (~1 GiB each). Fiber5–7 had
just finished. Evidence: `cold-root4-evidence`. Preserved.

Each fiber still decided `Finset.univ` on `Fin 4 → Fin 8` (4096
functions). Replaced with `Fin 8 × Fin 8 × Fin 8` (512 triples).
Public `highInputs_card` unchanged.
`gallai-zero-universe-split3` exit 0, wall 30.42 s, RSS 2,674,512 KiB;
fibers 8.4–11 s, parent 1.4 s. Not a cold default build.

Remaining large-Fin decides (same cert-file pattern):
`ThreeAnchorZeroOrbits` (`highZero_card` over `Fin 1024` plus
`∀ n : Fin 1024, HighZero n → … := by decide`) split into Core + 32
`BlockNN`; `ThreeAnchorCheapOrbits` (494 `decide`s in one file) split
into Core + 15 accept blocks. `gallai-cheap-zero-split1`–`split3` failed
parent packing proofs (not OOM). `gallai-cheap-zero-split4` exit 0, wall
3.08 s, RSS 1,982,868 KiB (blocks cached). Evidence:
`cheap-zero-split4-evidence`. Not a cold default build.

True cold default `lake build` of this source: `cold-source5` on
`/dev/vdb1[/gallai-cold-source5]`, snapshot 1133 files, no project
`.lake/build`. `gallai-cold-root5` OOM-killed 12:56:42 after ~10m,
cgroup anon ~5.74 GiB (systemd peak 4.0G under-counts). Victim lean
pid 117094 plus three peers: CompletedStarCoverage Block00–03 in
flight, ~1.4 GiB anon each. SizeTwoCoverage had not started. Evidence:
`cold-root5-evidence`. Preserved.

Repair: each 256-index coverage `decide` split into four Fin-64 `Sub`
files (CompletedStar, SizeTwo, ZeroSyndrome). Public `witness`
unchanged. `gallai-coverage-64-split1` exit 0, wall 12:16.58, `/usr/bin/time`
max RSS 3,153,164 KiB (~3.01 GiB), systemd 6.0G peak, swap 0, 1852 jobs.
Parents: CompletedStarCoverage, SizeTwoCoverage, ZeroSyndromeCoverage.
Evidence: `coverage-64-split1-evidence`. Not a cold default build.

True cold default `lake build` of this source: `cold-source6` on
`/dev/vdb1[/gallai-cold-source6]`, snapshot 1373 files, no project
`.lake/build`. `gallai-cold-root6` exit 0, 2622 jobs, wall 30:37.53,
`/usr/bin/time` max RSS 4,236,092 KiB (~4.04 GiB), systemd 5.3G peak,
swap 0. Challenge and Solution oleans present. Evidence:
`cold-root6-evidence` (SUCCESS marker written). The earlier standalone
NanoDa pass predates these splits and is not validation of this source.

PASSED: combined six-theorem Comparator/NanoDa `gallai-combined-replay-cold6`
on `cold-source6` under MemoryMax=6G, `enable_nanoda=true`, axioms
propext/Quot.sound/Classical.choice. Exit status 0, wall clock 37:19.28,
user 2197.06 s, maximum resident set size 2,748,304 KiB (~2.62 GiB), no
oom-kill. The log records `Lean default kernel accepts the solution`,
`nanoda kernel accepts the solution`, and `Your solution is okay!`. The only
warnings are six `declaration uses 'sorry'` sites in `Challenge.lean`
(lines 241, 254, 263, 271, 287, 297), which are statement stubs in the
challenge file and not solution obligations. Evidence:
`selected-replay-cold6-evidence/replay.log`. Not official Palomar
`verify_submission.py`.

### Commit authorization — 2026-09-14 Dubai

The two locally executable gates are green: `gallai-cold-root6` (exit 0,
2622 jobs, 30:37.53) and `gallai-combined-replay-cold6` (above). Every one
of the 1,370 tracked `.lean` and `.toml` files in this working tree was
hashed against `cold-source6` on the build VM, excluding vendored
`.lake/packages`, and the trees are byte-identical. The commit therefore
records exactly the source that both kernels accepted.

The third gate in the earlier authorization statement, `verify_submission.py`,
cannot precede the push. Its `prepare` entry point takes a GitHub dispatch
`--event` envelope and the workflow checks out `main` from the remote at a
commit, so it verifies an already-pushed commit by construction. The gate
ordering is corrected here: push first, then run official verification
against the pushed commit.

`Challenge.lean` carries local modifications relative to `f7e5917` and is
committed in the verified form. Two distinct changes: `exists_pathBudget` is
reproved through new public helpers `exists_singleEdgePath` and
`Decomposition.ofFamily`, leaving the statements of `Decomposition`,
`HasPathBudget` and `exists_pathBudget` untouched; and the `WholeBowtie`
`activePrivate`/`activity`/`syndrome` declarations plus the `TwoBowtie`
section header were rewritten from section `variable` binders to explicit
binders, with `[DecidableRel G.Adj]` added to the `TwoBowtie` header. The
second change alters signatures in the challenge interface and is not a
mechanical refactor. Comparator and NanoDa verify the solution against
whichever statement they are handed and cannot detect statement drift, so
their acceptance does not by itself establish that this file matches the
challenge as issued. This remains open for official verification to settle.

The targeted split build PASSED: 919 jobs, 62.12 seconds wall time, maximum
process RSS 1,851,476 KiB, exit 0; all 15 blocks and the selection consumer
built. The journal's 51.3 MiB cgroup peak is inconsistent with the process
RSS measurement and is not used as a reliable memory bound.

Resumed ordinary default build: `gallai-cold-root2` in `cold-source1`, same
6 GiB cap, no thread override. Only the tested OriginalOrbits parent and
15 block sources were copied from source; completed cold-root1 outputs were
retained. Evidence: `cold-root2-evidence/build.log`. This is a resumed build,
not a fresh cold run. The earlier standalone NanoDa pass predates this source
split and must be refreshed for the final candidate.

### Cold-root3 failure — 2026-09-14 10:09 guest time

The preceding `gallai-cold-root3` RUNNING state is superseded. The true cold
default `lake build` failed with systemd `Result=oom-kill`, 6 GiB cgroup peak,
and no result.json. Preserve `cold-root3-evidence/build.log` and
`source-hashes.json`. The last printed successful step was 1846/2200,
`SizeTwoCatalogue.Orbit166`; this is not the failed module. The Linux kernel
reports Lean PID 96607 killed with 5,106,736 KiB anonymous RSS and three
other concurrent Lean jobs. The killed command's module name was not captured,
so do not assign this failure to a particular certificate yet. Next gate:
capture in-flight Lean command lines in a guarded resumed build, identify the
fat module, then perform a targeted proof-term split and repeat cold validation.
Standalone NanoDa passed only for the earlier candidate; full Comparator/NanoDa
and exact Palomar replay remain unpassed. No commit or push.

RUNNING diagnostic: `gallai-cold-root3-diagnostic2` resumes the preserved
`cold-source3` build with `MemoryHigh=MemoryMax=6G`. Its two-second Lean
command snapshots are in `cold-root3-evidence/processes2.log`; build output
is `resumed-diagnostic2.log`. The first diagnostic service exited 127
immediately because its PATH omitted the prior service's Elan directory; its
log is preserved. Diagnostic2 uses that original HOME/PATH. This is a resumed
failure-localization run, not a fresh cold validation. It does not overwrite
`build.log` or the source hashes.

### Captured resumed-build OOM — 2026-09-14 11:25 guest time

The preceding RUNNING diagnostic is superseded. `gallai-cold-root3-diagnostic2`
failed with systemd `Result=oom-kill` at the 6 GiB memory cap. The two-second
process log maps kernel OOM victim PID 101575 to
`Gallai.Certificates.ZeroSyndromeUniverse`; its last captured RSS was
4,141,284 KiB total, and the kernel recorded 3,019,216 KiB anonymous RSS
at kill. `SizeTwoCatalogue` and `CompletedStarCoverage` jobs overlapped it.
The final printed completed step (2019/2043) does not identify the victim.
Evidence: `cold-root3-evidence/processes2.log`,
`resumed-diagnostic2.log`, and the kernel/systemd journals. This confirms a
parallel-build OOM involving `ZeroSyndromeUniverse`, not a Lean proof error.
Next gate: build that module alone under the same cap, then decide whether a
proof-term split is needed and repeat full cold validation.

RUNNING focused gate: `gallai-zero-universe-focused1` builds only
`Gallai.Certificates.ZeroSyndromeUniverse` from the preserved source tree,
under the same 6 GiB cgroup cap and without overlapping heavy workers. Output
is `cold-root3-evidence/zero-universe-focused1.log`. A pass would distinguish
parallel pressure from an individually unbuildable module, but would not
replace the cold default build gate.

The preceding focused RUNNING state is superseded: the target built
successfully (`1424/1424`, `ZeroSyndromeUniverse` 69 s, wall 71.77 s,
`/usr/bin/time` exit 0). Systemd reports a 1.8 GiB cgroup peak and zero swap.
The larger per-process maximum RSS is not additive because mapped pages are
shared. Thus the source is kernel-buildable alone, while default concurrent
Lake builds still OOM. The most expensive proof candidate in that 139-line
module is `highInputs_card : highInputs.card = 3047 := by decide`, which
checks the full four-row encoded domain. This is a candidate for targeted
proof-term splitting, not yet an established per-declaration profile. No
source repair, new cold pass, Comparator/NanoDa pass, or commit/push yet.
