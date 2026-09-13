# Bowtie removal in Gallai path decompositions

This is a substantive extracted Lean development for structural path-decomposition
results, prepared for a prospective Palomar entry. **Preparation is in progress;
this is not a registered or independently verified submission.**

A path decomposition partitions all edges of a finite simple graph into
nonempty simple paths. Gallai's conjecture asks for at most the ceiling of
half the vertex count in a connected graph. Here the even subgraph is induced
by vertices of even degree in the original graph. A whole bowtie is a full
component of that subgraph consisting of two triangles sharing one centre.

## Selected results

- **A:** removal of one whole bowtie in the presence of a second possible
  E-degree exception, under the four precisely stated sufficient alternatives.
  The endpoint conclusion is retained, including simultaneous exposure at odd order.
- **B:** full-incidence expansion of any degree-four hub costs exactly two
  additional paths and preserves the stated endpoint multiplicities. An explicit
  four-leaf-star example attains the additive-two path-number cost.
- **C:** simultaneous removal of arbitrarily many pairwise disjoint whole
  bowties in the stated supported class; shared odd anchors are allowed.
- **A1/A2:** the small-odd two-bowtie kernel is reducible; a counterexample in
  that kernel needs at least six odd vertices and sixteen vertices in total,
  with the stated exact boundary consequences.

The literal definitions and all six selected declarations are in Challenge.lean.
It imports only Mathlib, not the project proof library. Solution.lean imports
the extracted proofs. The six deliberate Challenge holes are not proof claims.
Comparator and independent-kernel verification are still required to establish
identity and readiness of this extracted package.

This does **not** prove the unrestricted two-exception conjecture. No novelty,
priority, independent human peer review, or journal acceptance is claimed.
The published input results used by the source development are formalized
dependencies, not newly claimed discoveries.

## Build and provenance

The exact Lean and Mathlib versions are pinned. Run `lake build` to build the
two independent Challenge/Solution roots. Do not import Challenge into Solution.
The source research project's eight paper deliveries passed its native formal
gates; that evidence is not a substitute for an extracted-project build or Palomar.

SOURCE_PROVENANCE.md and the two JSON inventories describe the exact extraction.
Only the source-import-reachable proof modules were included. The release has
no exploratory research tree, historical drafts, or all-module audit umbrella.

Licence: **Apache-2.0**, explicitly chosen by Idris Ali Shaik for this release.
Dependency licences remain their own. The code was developed with substantial
Codex assistance; kernel checking does not imply line-by-line human review.

See READINESS.md for the remaining gates. No public remote, push, submission,
or registration is implied by this local checkout.
