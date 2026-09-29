# Walkthrough: How TensorRocq Verifies a ZX Rewrite

## Context

You asked three questions about TensorRocq in the ZX setting:

1. Does it verify rewrites via hypergraph isomorphism?
2. Does that appeal to the matrix / tensor denotational semantics?
3. Can I walk through the relevant code?

**Short answers:** Yes, hypergraph isomorphism does the heavy lifting at run-time inside the tactic (it is the *decidable* check), but it is **only sound because** of a once-proved chain of lemmas connecting hypergraph isomorphism back to the tensor (matrix-like) denotational semantics. The verification is therefore a two-layer affair: a computational isomorphism test, justified by a denotational soundness theorem.

Note on terminology: TensorRocq's semantics map into `Tensor R n m A` — multi-index tensors over a `SemiRing`, which specialises to matrices over `C` for the ZX case. So "matrix denotational semantics" and "tensor denotational semantics" mean the same thing here.

The deliverable for this task is this explanatory document — no code changes.

---

## The three layers of the pipeline

TensorRocq sits on three stacked representations of a ZX (or any SMC) diagram:

```
   ZX term (e.g. VyZX `Z 1 2 0 ⟷ X 2 1 0`)
        │  DiagramQuote / DiagramDenote  (Examples/VyZXExample.v ~lines 181–445)
        ▼
   AProp T n m     (an inductive syntax for SMC terms)
        │  AProp_graph_semantics         (theories/Props/AProp/AProp.v:298)
        ▼
   CospanHyperGraph T n m   (graph + input/output interfaces)
        │  graph_semantics               (theories/Hypergraphs/CospanHyperGraph/Semantics.v)
        ▼
   Tensor R n m A   (the actual denotation — matrices for ZX)
```

Quotation goes ZX → AProp; the *semantic* mapping goes both AProp → Tensor (`AProp_semantics`) and AProp → Graph → Tensor (`graph_semantics ∘ AProp_graph_semantics`). The whole verification rests on showing those two routes give the same tensor.

---

## The user-facing tactic

In `Examples/VyZXExample.v` users write things like `zxrw lem at n` (line 471). The interesting tactics are:

- `zxrw lem at n` — rewrite by `lem` at the n-th match in the goal (line 469)
- `zxcat` — discharge a goal purely by hypergraph isomorphism (line 451)
- `zxclean_lhs` / `zxclean_rhs` — strip extraneous identity wires (lines 454–457)

These are thin instantiations of the generic SMC tactics in `theories/Translation/SemanticRewriting.v`:

```
Ltac zxrw lem match_num := wild_rw ZX_APROPlike ZXCCALC lem match_num.
Ltac zxcat              := wild_cat ZX_APROPlike ZXCCALC.
```

`ZX_APROPlike` packages the proof that VyZX's `≡` (proportionality) gives an APROP, and `ZXCCALC` is the tensor interpretation of the generators. With those two records, every generic SMC tactic in the library becomes a ZX tactic.

---

## What `zxrw` actually does (the verification core)

The body of `wild_rw_lhs` is `theories/Translation/SemanticRewriting.v:226`:

```rocq
Ltac wild_rw_lhs APROPlikeD TensT lem match_number :=
  match goal with
  |- ?R ?LHS _ =>
    unshelve epose proof (APROPlike_rewrite_helper_correctness
      (APROPlikeD:=APROPlikeD) (TensT:=TensT)
      match_number _ _ _ LHS _ _ _ _ _ lem _ _ _ _ _) as Hrw;
    [exact nil|];
    vm_eval (term_rewrite_helper _ _ _);     (* find the subterm *)
    vm_eval (graph_iso_partial_test _ _);    (* THE isomorphism check *)
    ...
```

Two evaluations happen by reduction in the kernel (`vm_eval` / `vm_compute`):

1. **`term_rewrite_helper`** picks an occurrence of the LHS pattern inside the goal and returns a context `(C1, C2)` such that the goal equals `C1 ∘ (id ⊗ pattern) ∘ C2`. This is purely syntactic on the AProp side.
2. **`graph_iso_partial_test`** then converts both "the actual goal subterm" and "the canonical rebuild `C1 ∘ (id ⊗ pattern) ∘ C2`" through `AProp_graph_semantics` into hypergraphs, and asks: are these hypergraphs isomorphic? If yes, the rewrite is licensed.

The hypergraph test lives at `theories/Hypergraphs/Isomorphism/Testing.v:1553`:

```rocq
Definition graph_iso_partial_test {n m} (cohg cohg' : CospanHyperGraph T n m) : bool :=
  match graph_isos cohg cohg' with
  | [] => false
  | _ :: _ => true
  end.
```

`graph_isos` (above it in the same file) is a **backtracking enumeration** of bijections on edges and vertices that respect labels, arity, and the input/output cospans. Returning a non-empty list means "we found at least one witnessing isomorphism."

The accompanying soundness lemma is at `Testing.v:1559`:

```rocq
Lemma graph_iso_partial_test_correct
  {n m} (cohg cohg' : CospanHyperGraph T n m) :
  graph_iso_partial_test cohg cohg' = true ->
  cohg ≡ₛ cohg'.
```

So if the boolean check returns true (which `vm_eval` will compute during tactic execution), we get the syntactic equivalence `≡ₛ` on hypergraphs — and that is exactly what is fed into the denotational story below.

---

## Where denotational semantics enters

Here is the answer to your second question — **yes, the soundness chain is denotational**.

### 1. Isomorphism ⇒ equal tensors

`theories/Hypergraphs/CospanHyperGraph/Facts.v:162`:

```rocq
Lemma graph_semantics_isomorphic {n m} (tg tg' : TensorGraph n m) :
  isomorphic tg tg' ->
  graph_semantics tg ≡@{@Tensor R n m A} graph_semantics tg'.
```

The proof unfolds `graph_semantics` (a sum-over-bound-indices of products of tensors named by hyperedges), uses the edge and vertex bijections from the isomorphism to relabel the sum, and shows the value is unchanged. This is the place where "two diagrams that look the same as hypergraphs really do denote the same matrix."

The definition of `isomorphic` itself is at `theories/Hypergraphs/CospanHyperGraph/Definitions.v:243`:

```rocq
Inductive isomorphic : relation CoHyGraph :=
  | iso_relabel_reindex tg fedge fvert
      `{Hfe : !Inj eq eq fedge} `{Hfv : !Inj eq eq fvert} :
      isomorphic tg (relabel_graph fedge (reindex_graph fvert tg)).
```

i.e. one graph becomes the other via injective relabelings of edge IDs and vertex IDs.

### 2. Lifting to syntactic equivalence

`≡ₛ` (`cohg_syntactic_eq`) is the closure of isomorphism plus a couple of book-keeping equivalences (`cohg_eq`, `cohg_vert_eq`). The combining lemma is `Facts.v:2321`:

```rocq
Lemma graph_semantics_syntactic_eq {n m} (cohg cohg' : TensorGraph n m) :
  cohg ≡ₛ cohg' ->
  graph_semantics cohg ≡ graph_semantics cohg'.
```

Each case dispatches to `graph_semantics_isomorphic` or a sibling — so `≡ₛ` is a *conservative* extension that still respects the tensor semantics.

### 3. Tying graph semantics back to AProp semantics

`theories/Props/AProp/AProp.v:311`:

```rocq
Lemma AProp_graph_semantics_correct {n m} (ap : AProp T n m) :
  graph_semantics (AProp_graph_semantics ap) ≡ AProp_semantics ap.
```

This proves the diamond commutes: interpreting an AProp term directly as a tensor (`AProp_semantics`, line 22) gives the same result as turning it into a hypergraph and then interpreting the hypergraph.

### 4. Finally, AProp ⇒ user-level diagram

The APROPlike interface (`theories/Props/AProp/APROPlike.v`) requires the user to prove that their concrete diagram language (here VyZX) interprets correctly via `DiagramQuote` / `DiagramDenote`. The combined statement `APROPlike_rewrite_helper_correctness` (`SemanticRewriting.v:69`) is the lemma `wild_rw_lhs` actually `epose`s. Reading lines 105–151, it literally:

- destructs the result of `term_rewrite_helper`,
- applies `graph_iso_partial_test_correct` to get `cohg ≡ₛ cohg'`,
- rewrites via `graph_semantics_syntactic_eq` and `AProp_graph_semantics_correct`,
- discharges the residual obligation with the SMC bifunctor laws for `compose_tensor_mor` / `stack_tensor_mor`.

---

## The full soundness chain for a `zxrw`

```
zxrw lem                                                      (VyZXExample.v:469)
   ↓
wild_rw_lhs ZX_APROPlike ZXCCALC lem n                        (SemanticRewriting.v:226)
   ↓ epose
APROPlike_rewrite_helper_correctness                          (SemanticRewriting.v:69)
   ↓ vm_eval
term_rewrite_helper apeTarg apeL n   →  Some (k, C1, C2)
graph_iso_partial_test
   (AProp_graph_semantics apeTarg)
   (AProp_graph_semantics (C1 ⟦id_k ⊗ lhs⟧ C2))    →  true    (Testing.v:1553)
   ↓ graph_iso_partial_test_correct                           (Testing.v:1559)
cohg ≡ₛ cohg'
   ↓ graph_semantics_syntactic_eq                             (Facts.v:2321)
graph_semantics cohg ≡ graph_semantics cohg'
   ↓ graph_semantics_isomorphic (key denotational step)       (Facts.v:162)
   ↓ AProp_graph_semantics_correct                            (AProp.v:311)
AProp_semantics goal ≡ AProp_semantics (C1 ∘ (id ⊗ rhs) ∘ C2)
   ↓ APROPlike interpretDiagram_correct                       (APROPlike.v)
ZX_LHS ∝ ZX_RHS                                               ✓
```

So `graph_iso_partial_test` is the *engine* (runs at every `zxrw`), and the four lemmas above are the *once-and-for-all* proof that the engine is sound w.r.t. the matrix denotation.

---

## A concrete reading order

If you want to walk through this in the source, here is a sensible order:

1. `Examples/VyZXExample.v:451–481` — see the user-facing tactics and how they wire into the generic framework.
2. `Examples/VyZXExample.v:488–529` — `hopf_rule_Z_X` is a worked proof that exercises `zxrw`, `zxclean_lhs`, and `zxcat` together.
3. `theories/Translation/SemanticRewriting.v:226–247` — `wild_rw_lhs`, the actual tactic body. See `vm_eval (graph_iso_partial_test _ _)` on line 239.
4. `theories/Translation/SemanticRewriting.v:69–152` — `APROPlike_rewrite_helper_correctness`, the lemma `wild_rw_lhs` uses; this is the cleanest place to *see* the soundness chain stitched together in one proof.
5. `theories/Hypergraphs/Isomorphism/Testing.v:1553–1569` — the isomorphism oracle and its correctness lemma. Read `graph_isos` and `hyperedge_map_monos_extending_aux` (just above) if you want to see the search.
6. `theories/Hypergraphs/CospanHyperGraph/Definitions.v:243` — what "isomorphic" means structurally.
7. `theories/Hypergraphs/CospanHyperGraph/Facts.v:162–203` — `graph_semantics_isomorphic`, the proof that isomorphic hypergraphs denote equal tensors. This is the *single most important denotational lemma* in the development.
8. `theories/Props/AProp/AProp.v:298–335` — `AProp_graph_semantics` and the `AProp_graph_semantics_correct` lemma proving the diamond commutes.
9. `theories/Props/AProp/AProp.v:9–36` — the `AProp` inductive and the direct tensor semantics `AProp_semantics`, for comparison.

---

## Verification

This is an explanatory task, not an implementation task — there is nothing to test, build, or run. The "verification" is that the explanation matches the source; the file paths and line numbers above were checked directly against the files at the time of writing.
