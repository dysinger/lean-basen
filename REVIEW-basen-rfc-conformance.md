# REVIEW — `basen-rfc-conformance-theorems`

Independent, adversarial review of the just-landed work:
`lean-basen` commits `9babcab`, `6d7ba52`, `44c0edf`, `c0c55cd`, `bff89f0`;
`lean-codec` commits `1e9207e`, `0838001`, `0a1c5dd`.

Scope reviewed:

- `BaseN/Base64.lean` (2545 lines) — new: `relB64Block_all_size3`, `b64Split_blocks_tail`,
  `encodeB64Tail_of_rel`, `decodeFullB64_conv`, `encodeB64_injective`.
- `BaseN/Base32.lean` (2922 lines) — mirrors of the above.
- `Bench.lean` (188 lines) — rewritten.
- change artifacts `openspec/changes/basen-rfc-conformance-theorems/{proposal,design,tasks,specs}`
- synced `openspec/specs/basen/spec.md`, `lean-codec/{PAPER,README,AGENTS}.md`, `lean-basen/AGENTS.md`

---

## 1. Severity-ranked findings

### CRITICAL

**C1 — `Bench.lean` "canonical" examples are tautologies; they verify nothing.**

`Bench.lean:110-137`. The two canonical examples:

```
example (n s ...) (he : Base64.encodeB64 foobar = some ⟨n, s⟩) :
    ∃ blocks m₁ m₂ blkBytes tailBytes,
      encodeRepeat b64BlockElem blocks = some ⟨m₁, blkBytes⟩ ∧
      encodeB64Tail (...) = some ⟨m₂, tailBytes⟩ ∧
      List.ofFn s = List.ofFn blkBytes ++ List.ofFn tailBytes := by
  obtain ⟨blocks, m₁, m₂, blkBytes, tailBytes, hblk, htail, hlen, _, _⟩ :=
    Base64.encodeB64_canonical foobar he
  exact ⟨blocks, m₁, m₂, blkBytes, tailBytes, hblk, htail, hlen⟩
```

This is a pure unpack-and-repack of `encodeB64_canonical`'s own ∃-hypothesis. It
**drops conjuncts 4 and 5** of the source theorem
(`Base64.lean:2230-2235`) — the only two that say anything about the RFC:
"every byte alphabet-valid" and "the tail is exactly `[c₀,c₁,=,=]`/`[c₀,c₁,c₂,=]`".
So the bench does **not** value-check `Zg==`/`Zm8=`/`Zm9v`/`MY======`/`MZXW6YTB`
byte-for-byte through the uniform encoder at all — it re-states the decomposition
of whatever `encodeB64` happened to produce. A buggy `encodeB64` (e.g. emitting
lowercase or wrong pad arity) would still satisfy this `example`. Task 5.1 claims
"canonical vectors (`Zg==`/`Zm8=`/`Zm9v`, `MY======`/`MZXW6YTB`) … all through
`Codec.encode`" — that claim is **false**: those strings never appear anywhere in
`Bench.lean` as an expected-encoder-output assertion (only as `b64BlockUnapply`
block-level `#eval`-style `rfl`s, which test `b64BlockUnapply`, not `encodeB64`).
**Why it matters:** the gate is supposed to "value-check each rejection/canonical
vector byte-for-byte" (spec `… gated …`, Scenario "The gate covers the new laws").
It does not. **Fix:** assert concretely
`example : Base64.encodeB64 foobar = some ⟨8, ⟨…"Zm9vYmFy"…⟩⟩ := rfl` (or a
decide-checked `List.ofFn`), i.e. pin the _actual_ encoder output for each of
`f/fo/foo/foob/fooba/foobar`, and likewise base32. Do not route through the ∃-theorem.

**C2 — `encodeB64_injective` does NOT state the spec's injectivity law.**

Spec (`changes/…/specs/basen/spec.md:134-138`):

> "**WHEN** `encode{X} v = encode{X} v'` (or `Codec.encode <codec> v = Codec.encode <codec> v'`) … **THEN** `v = v'`"

Code (`Base64.lean:2538`):

```
theorem encodeB64_injective {v v' : List UInt8} {n : Nat} {s : Bytes n}
    (h : encodeB64 v = some ⟨n, s⟩) (h' : encodeB64 v' = some ⟨n, s⟩) : v = v'
```

The code assumes **both** encodes _succeed to the same witness_, not `encode v =
encode v'` as `Option` equality. The gap is the `none = none` branch: `Option`
equality implies `v = v'` only if at least one side is `some` **or** `encode v =
none` is impossible. The code never proves `encodeB64 v ≠ none` (there is no such
theorem; grep found none). Enumeratively `encodeB64` appears total
(`#eval (encodeB64 …).isSome` = `true` for `[]`, `[0x66]`, `[0x66,0x6F,0x6F]`,
`replicate 7`, `replicate 100`), so the _intended_ law is true — but it is **not
what is proved**. A reader checking the spec's scenario literally against Lean will
find a strictly weaker statement with an unproved-and-unstated bridging fact
(`encode` is total). This is the same shape for `encodeB32_injective`
(`Base32.lean:2915`) and the five fixed-width `encode_injective`
(`Base2:561`, `Base4:455`, `Base8:589`, `Base10:411`, `Base16:399`) — all take
`… = some ⟨n,s⟩` twice.
**Why it matters:** the spec's stated law is a claim about `encode`, matching the
paper's "partial isomorphism"; the code states a law about _pairs of successful
encodings_ and silently relies on totality. **Fix:** either (a) restate the theorem
as `encodeB64 v = encodeB64 v' → v = v'` (discharge the `none` branch from a new
`encodeB64_isSome`/`encodeB64_ne_none` lemma), or (b) amend the spec's scenario to
"... both = `some ⟨n,s⟩`" and **add** the totality lemma `encodeB64 v ≠ none` so the
weakening is honest. Do not leave the spec sentence as-is.

**C3 — Synced base spec still asserts the _withdrawn_ "unrepresentable" claim and
"no per-format function" while the code has both.**

`lean-codec/openspec/specs/basen/spec.md:24-31` (synced main spec):

> "… composition of a full-block `Codec (List UInt8)` run + a terminal-tail
> `Codec`, `iso`-ed to the terminal-tail value type `B32`/`B64`, **so illegal
> "data after `=`" is unrepresentable**) … and no bespoke `encode`/`decode`."

Two falsehoods, both admitted by the change itself elsewhere:
(i) The proposal (`proposal.md` Impact) explicitly **withdraws** "unrepresentable":

> "(The earlier "re-typing makes the shape unrepresentable" and "no bijective
> flattening exists" claims were false … and are withdrawn.)"
> (ii) The code has bespoke whole-input functions `decodeFullB64`/`encodeB64`
> (`Base64.lean:865,919`), `decodeFullB32`/`encodeB32` — not `Codec.decode`/
> `Codec.encode` applied to a single value. The main spec's scenario (`:33-37`) says
> "there is no `BaseN.Base16.decode`-style per-format function" — but
> `BaseN.Base64.decodeFullB64` **is** exactly such a per-format function.
> **Why it matters:** the _synced, authoritative_ spec now contradicts the change's
> own delta spec and the code. A downstream consumer reading the main spec is misled
> both ways. **Fix:** archive-time reconcile — add a MODIFIED block on "The `basen`
> bases are `Codec` values" removing "unrepresentable" and qualifying "no bespoke
> per-format function" as "no per-format _decoder triple_; whole-input base32/64
> expose `decodeFullB{32,64}`/`encodeB{32,64}` composition functions" (or actually
> remove those functions by making them `abbrev`/`def` wrappers documented as the
> composition, which is what D7/D8 promise).

### HIGH

**H1 — `decodeFullB64`/`decodeFullB32` are still the `head?`/`filterMap` shape that
D7 claims to have _removed_.**

`Base64.lean:865-871` and `Base32.lean:1008-1013`:

```
def decodeFullB64 {n} (s : Bytes n) : Option (List UInt8) :=
  List.head? ((decodeRepeat b64BlockElem b64BlockConsumesByte n s).filterMap fun ⟨blocks, t⟩ => …)
```

Design `design.md:237` header: "…**not** `head?`/`filterMap`"; `:276` "This removes
the flattened `List UInt8`/`head?`/`filterMap` step". **Both are false** — the exact
shape remains. The only honest note is buried in a task parenthetical
(`tasks.md:160-163`): "(the D7 rewrite is not required for the law, only for the
… wording)". **Why it matters:** a reviewer trusting D7's "not head?/filterMap"
conclusion will believe a code restructuring that did not happen. It also means the
`head?`-picks-the-first-`filterMap`-hit determinism still rests on the
`boundary_pin`/`head?_eq_some_of_mem_eq` machinery D7 said would be gone.
**Fix:** either perform the D7 rewrite, or rewrite D7 to say "kept `head?`/
`filterMap`; guarded by `≤ 1` (D8); the composition exists only under the hood" and
delete the "not `head?`/`filterMap`" header assertion.

**H2 — Bench `rejects_lowercase` as a _passing_ example contradicts the proposal's
explicit non-goal.**

`Bench.lean:181-184`:

```
-- Base16 non-goal (recorded, not a passing vector): lowercase `6f` is rejected.
example : Codec.decodeFull Base16.hexElem Base16.hexConsumesByte 1 (fun _ => 0x66) = none :=
  Base16.rejects_lowercase
```

This comment calls itself "not a passing vector" and it is a **passing** `example`.
The proposal (`proposal.md`, Bench bullet) says lowercase is "recorded as a
non-goal, **not** a passing vector." A green `example` proving lowercase `0x66`
(i.e. 'f', not '6f') is rejected _is_ a passing vector asserting the decoder rejects
lowercase — precisely the RFC §8 "MUST accept both cases" behaviour the project
declares out of scope. **Why it matters:** the bench enshrines a non-conformance as
a positively-tested fact. That is defensible only if it is labelled as such _and_
the spec/scenario acknowledges RFC §8 divergence — the change specs do not mention
§8 at all. **Fix:** either delete the `example` entirely (record the divergence in
the spec as a documented RFC §8 non-conformance), or keep it and add a spec
"Requirements: base16 is uppercase-only (RFC §8 divergence)" requirement. Also the
inline comment says "lowercase `6f`" but the byte is `0x66` = `'f'` — the
word "lowercase `6f`" is wrong (it's the single char `f`, and the comment claims a
_string_ `6f` is rejected; the theorem is about a single `f`).

**H3 — `relB32Block_all_size3` proves length **5**; `relB64Block_all_size3` proves
length **3**. The shared name lies for base32.**

`Base64.lean:2291`: `… → ∀ b ∈ blocks, b.length = 3`
`Base32.lean:2664`: `… → ∀ b ∈ blocks, b.length = 5`
Same name, different content. Base32 blocks are 8 chars = 5 bytes; the name says
"size3". **Fix:** rename to `relB64Block_len3` / `relB32Block_len5`, or
`relB{32,64}Block_all_len` with a per-file comment.

**H4 — Duplicated generic lemmas that belong in `Common.lean`.**

- `b64Split_blocks_tail` (`Base64.lean:2314`) vs `b32Split_blocks_tail`
  (`Base32.lean:2685`) are structurally identical except the block-size (3 vs 5)
  and tail bound (2 vs 4). Both prove: `b64Split` of `blocks.flatten ++ tail`
  recovers `(blocks, tail)` given `∀ b ∈ blocks, b.length = k` and
  `tail.length < k`.
- `encodeB64Tail_of_rel` (`Base64.lean:2355`) vs `encodeB32Tail_of_rel`
  (`Base32.lean`) — same proof shape (functionality of the tail element pins the
  bytes), differing only in the element (`b64TailElem` vs `b32TailElem`), the tail
  shapes (1–2 vs 1–4 bytes), and the encoder fn.
- `relB64Block_all_size3` vs `relB32Block_all_size3` — identical induction.

**Proposed generic statements (in `BaseN.Common`):**

```lean
theorem relRepeat_all_len {α} (elem : Codec (List UInt8)) (len : Nat)
    (h : ∀ x {m} (s : Bytes m), Rel elem x s → x.length = len)
    {blocks : List (List UInt8)} {m : Nat} (s : Bytes m) :
    relRepeat (Rel elem) blocks m s → ∀ b ∈ blocks, b.length = len

theorem split_flatten_app (split : List UInt8 → (List (List UInt8) × List UInt8))
    (hk : ∀ l, … rectangular k, tail < k → split l = …) …
```

(A generic `split_blocks_tail (k : Nat)` parameterized by the per-file
`{b64,b32}Split`'s defining equations, and a generic
`encodeTail_of_rel {elem : Codec (List UInt8)} (functional : …)`.)
**Why it matters:** this is exactly the "each base reuses `BaseN.Common` instead of
re-deriving them" AGENTS.md rule (`lean-basen/AGENTS.md`, "Common.lean — the shared
generic … lemmas … Each new base `open BaseN.Common` and reuses these instead of
re-deriving them"). The change re-derives 3× per base. **Fix:** hoist to Common
with the parameters above, and document why a fully-generic version isn't possible
(the `Rel`-driven length hypothesis can be parameterized; the split-back needs the
particular `split` definition). Flag as tech-debt at minimum.

### MEDIUM

**M1 — `#print axioms` all clean; no leaks. (Positive confirmation, but the check
is not automated.)**

Actual output (`/tmp/chk.lean`, `lake env lean`):

```
'BaseN.Base64.relB64Block_all_size3' depends on axioms: [propext, Quot.sound]
'BaseN.Base64.b64Split_blocks_tail' depends on axioms: [propext]
'BaseN.Base64.encodeB64Tail_of_rel'  depends on axioms: [propext, Quot.sound]
'BaseN.Base64.decodeFullB64_conv'    depends on axioms: [propext, Quot.sound]
'BaseN.Base64.encodeB64_injective'   depends on axioms: [propext, Quot.sound]
'BaseN.Base32.relB32Block_all_size3' depends on axioms: [propext, Quot.sound]
'BaseN.Base32.b32Split_blocks_tail'  depends on axioms: [propext]
'BaseN.Base32.encodeB32Tail_of_rel'  depends on axioms: [propext, Quot.sound]
'BaseN.Base32.decodeFullB32_conv'    depends on axioms: [propext, Quot.sound]
'BaseN.Base32.encodeB32_injective'   depends on axioms: [propext, Quot.sound]
```

No `Classical.choice`, no `sorryAx`. **But** this is manual, not gated; the AGENTS
"`#print axioms Codec.roundtrip` is the check" is _not_ what is being run here —
only the lean-basen laws. Add a CI `Axioms.lean` that `#print axioms` every new
law so a future proof regression (a `simp` picking `Classical.choice`) trips the
build. (The `Classical.choice` leak was already found _once_ in this session per
`tasks.md:184`; it will recur.)

**M2 — `decodeFullB64_conv` does faithfully state the spec's converse law, but the
`s = ⟨n, s⟩` is the _input's_ length and cannot be anything else.** This is
correct: spec says "reproduces `s` byte-for-byte". Confirmed YES (see §2). No issue.
The only nit is `decodeFullB64_conv`'s `n` is implicit in `s : Bytes n` — good.

**M3 — No "unique canonical" is actually proved beyond converse+injectivity.** The
requirement is titled "Decode is the unique canonical inverse" (spec:114). The body
only delivers (a) `decode (encode v) = some v` (roundtrip), (b) `decode s = some v →
encode v = s` (converse), (c) `encode v = encode v' → v = v'` (injectivity, in the
weakened C2 form). These imply "unique" only if `encode` is total and the decoder's
success-set is exactly `encode`'s image — i.e. a "decode succeeds iff s ∈ image
encode" theorem, which is **not** stated. The rejection theorems cover _specific_
bad vectors, not "decode s = none ↔ s ∉ image(encode)". So the spec's headline
"unique inverse / total characterization / decode succeeds _exactly_ on the
RFC-valid inputs" (proposal Why) is not delivered. **Fix:** state
`decodeFullB64 s = some v ↔ ∃ v', encodeB64 v' = some ⟨n, s⟩` (or the `none ↔ ∉ image`
form) as an explicit theorem; that is the actual "total characterization," and it
subsumes the specific rejections. Add as a new task.

**M4 — Rejection family is finite examples, not the Ω-statement the proposal
promises.** Proposal Why: "the _whole-string arity_, and any data after the
terminal `=` run … proved as an inequation over the whole-input composition by the
pad-dichotomy." The actual theorems are named vectors: `reject_ZgAAAA`,
`reject_MYAAAA`, `reject_invalid_char`, `reject_pad_first`, `reject_bad_length`,
plus `reject_first_invalid` and `reject_overflow`. There is **no** general theorem
"`∀ s, ¬ valid s → decode s = none`" nor "`∀ s l, b64BlockElem`-run-only `s` →
…". So "the decoder is a total characterization" is rhetoric; the code proves
specific counter-example vectors. **Fix:** state the general
`decodeFullB64 s = none` for (a) any `s` with a byte `b64Valid = false` (a general
version of `reject_first_invalid` for _all_ positions, not just index 0),
(b) any `s` with `=` not in the terminal tail (general), (c) any `s` with
`n % 4 ≠ 0`. These are what RFC conformance means; the current vectors are the F\*
reference's _test set_, not the theorem.

**M5 — Spec's `head?`/`filterMap` sentence is _accurate_ to the code but falsifies
D7.** spec:43 "the whole-input decoder is `List.head? ((decodeRepeat {x}Elem …).filterMap
(decodeFull {x}TailElem …))`". This exactly matches `Base64.lean:865`. So the _spec_
is fine; the _design_ is the lie (H1). No spec drift on this point — but the design
must be corrected. Do not "fix" the spec to match a rewrite that did not happen.

### LOW

**L1 — `subst hst_eq` and `simp only [Suffix.empty, Nat.sub_zero] at st hrelt` are
brittle.** `Base64.lean:2455` (`simp only [Suffix.empty, Nat.sub_zero] at st hrelt`)
and `:2487` (`subst hst_eq`). These depend on:

- `Suffix.empty` unfolding to a structure whose `.remaining` reduces to `0` via
  `Nat.sub_zero` — fine now, but a `Suffix` field rename or a mathlib-style
  re-ordering of `sub_zero` break it.
- `subst hst_eq` where `hst_eq : st = t.bytes` — `subst` rewrites `st` everywhere
  including `henct`; sound, but `subst` is being used to transport a _type_
  (`st : Bytes t.remaining`) not just a value; `subst` here works only because
  `t.remaining` is `st`'s type index and `t.bytes` has the same index. It is
  Lean-robust only insofar as the `simp only` left the type as `Bytes t.remaining`.
  Prefer `cases hst_eq` / `rw` or an explicit `cast` with `Nat.sub_zero`.
- `dsimp only []` at `:2477` is a no-op — remove it.

**L2 — The 4-branch `rcases x with _ | ⟨a, t⟩; cases t with …` cascade in
`encodeB64Tail_of_rel` (`:2405-2422`) is overkill; a length-dichotomy is 3 lines.**
`Rel_b64TailElem_size x st hrelx : x.length = 1 ∨ x.length = 2` is _already in
scope_ (line `:2397`). The tail branches only need to establish
`encodeB64Tail x = Codec.encode b64TailElem x` for a 1- or 2-element list. Proposed
alternative:

```lean
have hxf : encodeB64Tail x = Codec.encode b64TailElem x := by
  match x, hxlen with
  | [a], _ => rfl
  | [a, b], _ => rfl
  | [], h => simp at h    -- impossible
  | a :: b :: c :: _, h => simp at h
rw [hxf]; exact he
```

(or just `cases x <;> cases hxlen <;> first | rfl | omega`). The current cascade
duplicates the length check three times per shape.

**L3 — `relB64Block_all_size3` and `b64Split_blocks_tail` take `blocks`/`m`/`s` as
_explicit_ (not implicit) or odd-position arguments.** `relB64Block_all_size3`
takes `{blocks} {m} (s : Bytes m)` — fine. `b64Split_blocks_tail` takes
`(blocks) (tail) (hblocks) (htail)` — all explicit; call sites are verbose. Prefer
`{blocks} {tail}`. NIT.

**L4 — `decodeFullB64_some`'s ∃-shape exposes `tails.length ≤ 1` as a conjunct, but
`decodeFullB64_conv` consumes it as `hlen`.** Correct, but the reader must discover
that the `≤1` guard (D8) is _the reason the converse is unconditional_. Add a
docstring line in `decodeFullB64_conv` explicitly citing D8, because without D8 the
theorem is false (design's `Zg==Zg==` counterexample). Currently the docstring
(`:2423-2429`) mentions `tails.length ≤ 1` only in passing.

**L5 — `Bench.lean` has no base2/4/8/10 or base32/64 _roundtrip_ value-check
through the encoder.** `Bench.lean:59-73` uses `b{32,64}BlockUnapply` (block-level),
not `encodeB64`/`encodeB32`. The only whole-input proofs are the polymorphic
`example (n s) (h : encodeB64 foobar = some ⟨n,s⟩) : decodeFullB64 s = some foobar`
(`:83-90`). This is _better_ than nothing but still not a byte-value check: it
never names the expected output string. See C1.

**L6 — `rejects_lowercase`'s theorem (Base16.lean:436) is one specific vector,
not the RFC §8 non-conformance it is filed under.** It proves `decodeFull … 1
(fun _ => 0x66) = none` (byte `f` rejected) — but the RFC §8 requirement is that a
decoder MUST accept lowercase; a fuller non-conformance vector would be
`decodeFull … 2 ("6f")`, i.e. the two-byte uppercase-equivalent. The current theorem
does not even state the interesting case. **Fix:** also state
`decodeFull hexElem … 2 "6f" = none` if lowercase two-char forms are rejected (they
are, per the strict uppercase `Iso`), and label both as the RFC §8 divergence.

### NIT

**N1 — `<openai>` typo?** No — no such string. Ignore. _(No such defect found.)_

**N2 — `Bench.lean:181` comment says "lowercase `6f`" but the byte is `0x66` (`'f'`).**
`0x66` is `'f'`, not the two-char string `"6f"`. Fix the comment.

**N3 — `encodeB64_injective` docstring says "a partial bijection" (correct only if
combined with totality, which is unproved).** `:2535-2536`: "so `decodeFullB64` is
the left inverse and `encodeB64` a partial bijection." "Partial bijection" implies a
_bijection between domain and image_; the proof only shows injectivity, and
`encodeB64`'s totality is unproved. Docstring overstates (see C2).

**N4 — `design.md` D8 says "LANDED `../lean-basen` `c0c55cd`" but the commit is
absent from `git log` output?** Verify: `git log` shows `c0c55cd` ("single-block
terminal-tail guard (D8)") — present. No defect.

---

## 2. Per-theorem: does it faithfully state the spec law?

| Theorem                               | Spec law (quote)                                             | Lean statement                                                  | Faithful?                                                                 |
| ------------------------------------- | ------------------------------------------------------------ | --------------------------------------------------------------- | ------------------------------------------------------------------------- |
| `decodeFullB64_conv` (B64.lean:2430)  | "…returns `some v` … **THEN** `encode{X} v … = some ⟨n, s⟩`" | `decodeFullB64 s = some v → encodeB64 v = some ⟨n, s⟩`          | **YES** — `s` is the input's own `Bytes n`; byte-exact.                   |
| `decodeFullB32_conv` (B32.lean:2825)  | same                                                         | same                                                            | **YES**                                                                   |
| `encodeB64_injective` (B64.lean:2538) | "**WHEN** `encode v = encode v'` … **THEN** `v = v'`"        | `encodeB64 v = some ⟨n,s⟩ → encodeB64 v' = some ⟨n,s⟩ → v = v'` | **NO** — takes both `some`, misses `none = none`; totality unproved (C2). |
| `encodeB32_injective` (B32.lean:2915) | same                                                         | same                                                            | **NO** (same)                                                             |
| `Base16.decode_encode_inverse` (:384) | converse for fixed-width                                     | `decodeFull hexElem … s = some v → encodeHex v = some ⟨n,s⟩`    | **YES**                                                                   |
| `Base16.encode_injective` (:399)      | injectivity                                                  | both `= some ⟨n,s⟩`                                             | **NO** (same shape as C2)                                                 |
| `Base2/4/8/10` `encode_injective`     | same                                                         | same                                                            | **NO** (same)                                                             |
| `relB64Block_all_size3`               | canonical "block is 3 bytes"                                 | `b.length = 3`                                                  | YES (content; name correct for B64)                                       |
| `relB32Block_all_size3`               | canonical "block is 5 bytes"                                 | `b.length = 5`                                                  | content YES, **name FALSE** (H3)                                          |
| `b64Split_blocks_tail`                | (helper)                                                     | split-back                                                      | helper, correct                                                           |
| `encodeB64Tail_of_rel`                | (helper)                                                     | tail re-encode                                                  | helper, correct                                                           |

**"Unique canonical inverse" (spec requirement title)**: NO single theorem states
`decode s = some v ↔ ∃ v', encode v' = some ⟨n,s⟩`, i.e. the "total characterization"
the proposal headlines. See M3. Converse + injectivity + roundtrip are three
_separate_ laws; they do not compose to "unique" without the iff.

**`tails.length ≤ 1` guard consistency**: the D8 guard is what makes the converse
TRUE (design: `Zg==Zg==` counterexample). It is consistent with the rejection
flagship (`reject_ZgAAAA`) and with the converse — because the guard rejects the
multi-block tail class. But the two-block-pad class `Zg==Zg==` is rejected by
returning `none` — that is a `decodeFull s = none` for an `s` the _rejection_ family
does not name (only `reject_bad_length`/`reject_ZgAAAA`). So the rejection family
should name `Zg==Zg==` too. It is _implicitly_ handled (the `≤1` guard) but no
theorem states `decodeFullB64 "Zg==Zg==" = none`. Add it (M4).

---

## 3. `#print axioms` results (actual command output)

Command: `nix develop --command lake env lean /tmp/chk.lean` on
`/Users/user/_/lean-basen`:

```
'BaseN.Base64.relB64Block_all_size3' depends on axioms: [propext, Quot.sound]
'BaseN.Base64.b64Split_blocks_tail' depends on axioms: [propext]
'BaseN.Base64.encodeB64Tail_of_rel' depends on axioms: [propext, Quot.sound]
'BaseN.Base64.decodeFullB64_conv' depends on axioms: [propext, Quot.sound]
'BaseN.Base64.encodeB64_injective' depends on axioms: [propext, Quot.sound]
'BaseN.Base32.relB32Block_all_size3' depends on axioms: [propext, Quot.sound]
'BaseN.Base32.b32Split_blocks_tail' depends on axioms: [propext]
'BaseN.Base32.encodeB32Tail_of_rel' depends on axioms: [propext, Quot.sound]
'BaseN.Base32.decodeFullB32_conv' depends on axioms: [propext, Quot.sound]
'BaseN.Base32.encodeB32_injective' depends on axioms: [propext, Quot.sound]
'BaseN.Base64.decodeFullB64_roundtrip' depends on axioms: [propext, Quot.sound]
'BaseN.Base32.decodeFullB32_roundtrip' depends on axioms: [propext, Quot.sound]
'BaseN.Base64.decodeFullB64_reject_ZgAAAA' depends on axioms: [propext, Quot.sound]
'BaseN.Base32.decodeFullB32_reject_MYAAAA' depends on axioms: [propext, Quot.sound]
'BaseN.Base64.encodeB64_canonical' depends on axioms: [propext, Quot.sound]
'BaseN.Base32.encodeB32_canonical' depends on axioms: [propext, Quot.sound]
'BaseN.Base16.decode_encode_inverse' depends on axioms: [propext, Quot.sound]
'BaseN.Base16.encode_injective' depends on axioms: [propext, Quot.sound]
```

**No `Classical.choice`, no `sorryAx`, no `native_decide`.** The `[propext, Quot.sound]`
claim is **CONFIRMED** for every theorem in scope. The `[propext]`-only row for the
two split-back lemmas is even cleaner than required.

`grep` for `sorry|admit|native_decide|Classical.choice|by_contra|implemented_by` in
`BaseN/Base64.lean`, `BaseN/Base32.lean`, `Bench.lean`: all hits are in docstrings
("zero `sorry`", "`Classical.choice`-dependent" explanatory text) or benign
`decide` (which is a `Decidable` reduction, not `native_decide`). **No cheat.**

---

## 4. Proposed NEW openspec tasks

### In `basen-rfc-conformance-theorems` (reopen — currently `status: complete` is

### premature):

- [ ] 6.1 **Fix the bench canonical tautology (C1).** Replace the two ∃-unpacking
      `example`s in `Bench.lean` with concrete byte-value asserts:
      `example : Base64.encodeB64 foobar = some ⟨8, ⟨"Zm9vYmFy" as Bytes 8⟩⟩ := rfl`
      (and for `f/fo/foo/foob/fooba`; likewise base32 `MY======`/`MZXW6YTB`).
      Verify `rfl` or `decide`; if `rfl` fails, use `by decide` or an explicit
      `List.ofFn` equality. Gate test: a deliberately-wrong `encodeB64` (lowercase)
      MUST fail this bench.
- [ ] 6.2 **Restate injectivity as the spec's law (C2).** Add
      `encodeB64_isSome : (encodeB64 v).isSome` (or `≠ none`) and restate
      `encodeB64_injective` as `encodeB64 v = encodeB64 v' → v = v'`. Mirror for
      base32 + the five fixed-width bases. **OR** amend the spec's "Encoding is
      injective" scenario to "both = `some ⟨n,s⟩`" and add the totality lemma. Do not
      leave the spec sentence mismatched.
- [ ] 6.3 **Add the "unique canonical / total characterization" iff (M3).**
      `decodeFullB64 s = some v ↔ ∃ v', encodeB64 v' = some ⟨n, s⟩ ∧ v = v'`
      (or the `none ↔ ∉ image(encode)` form). This is what "unique canonical
      inverse" actually means; the current converse+injectivity is strictly weaker.
- [ ] 6.4 **Generalize the rejection family (M4).** Prove, for all `s`:
      (a) `(∃ i, b64Valid (s i).toNat = false) → decodeFullB64 s = none`
      (not just `s 0`);
      (b) `∃ i < n, s i = 61 ∧ i < n - 3` (non-terminal `=`) → `decodeFullB64 s = none`
      (the general `=`-position law, covering `Zg==Zg==` explicitly);
      (c) `n % 4 ≠ 0 → decodeFullB64 s = none`. Mirror base32. This is the actual
      RFC-4648 conformance; the named vectors are its instances.
- [ ] 6.5 **Correct design.md D7 (H1).** Either perform the D7 rewrite (remove
      `List.head?`/`filterMap` from `decodeFullB64`/`decodeFullB32`) or rewrite D7's
      header ("**not** `head?`/`filterMap`") and body to say the shape is retained,
      guarded by `≤ 1`. As written D7 lies.
- [ ] 6.6 **Reconcile the synced main spec (C3).** Add a MODIFIED block on
      "The `basen` bases are `Codec` values" dropping "unrepresentable" and
      qualifying the "no bespoke per-format function" claim to name
      `decodeFullB{32,64}`/`encodeB{32,64}` as composition entry points, OR rewrite
      those as `abbrev`s over the composition. Add a non-goal / spec requirement for
      the base16 RFC §8 divergence.
- [ ] 6.7 **Rename `relB32Block_all_size3` → `relB32Block_len5` (H3)** (and
      `relB64Block_all_size3` → `relB64Block_len3` for symmetry).
- [ ] 6.8 **Hoist the duplicated helpers to `Common.lean` (H4)**: generic
      `relRepeat_all_len {elem} {len} (h : ∀ x {m} s, Rel elem x s → x.length = len)`
      and a parameterized split-back; at minimum add a docstring in each base noting
      the mirror and why it is per-base (the specific `split` def).
- [ ] 6.9 **Add an automated axiom-gate file** `Axioms.lean` (or `#print axioms`
      block in `Bench.lean`) covering _every_ new law, so a future `Classical.choice`
      regression fails `lake build`. The AGENTS "codec-roundtrip axiom" claim is not
      what is run.
- [ ] 6.10 **Fix the `rejects_lowercase` comment and add the RFC §8 divergence
      statement (H2, L6).** State two-char `"6f"` rejection and record the §8
      non-goal in `specs/basen/spec.md`.

### In a new change `basen-rfc-total-characterization` (follow-on):

- [ ] 7.1 The general "decode succeeds iff s ∈ image(encode)" iff (from 6.3/6.4).
- [ ] 7.2 If the "unrepresentable" claim is to be resurrected legitimately, prove
      a _type-level_ `B64` that cannot represent trailing data (currently it is a
      bijective relabeling of `List UInt8`, so "unrepresentable" is false by
      construction). Otherwise keep the withdrawal and update the main spec.
- [ ] 7.3 Base16 case-insensitive decoder (RFC §8 "MUST accept both cases") —
      currently a non-goal; if ever pursued, it breaks `Unambiguous` (per design) and
      needs a documented relaxation.

---

## 5. Unverifiable / not checked

- **PAPER.md §4.3 "partial isomorphism"** vs the code: the paper's `PartialIso`
  has `apply`/`unapply`/`law_apply_unapply`/`law_unapply_apply`. `decodeFullB64_conv`
  - `decodeFullB64_roundtrip` give both directions _on the domain of `encode`_ only
    if the "decode = none iff not in image" half holds — which is unproved (M3). So
    "the paper's partial isomorphism" claim (proposal) is unverifiable from the code as
    it stands.
- **Bench runtime**: `Bench.lean` `main` is `pure ()` — there is no runtime smoke
  check; only type-checking. The `example`s are proofs, so "value-checks" means
  proof-checking, not `#eval`-ing bytes. That is fine for correctness but means the
  bench adds no _independent_ oracle; it only re-derives. (This is C1's root cause.)
- **`lean-codec`'s `encode_of_decode`/`bidir`**: the prompt claims design 4.3 says
  `(bidir b64TailElem …).2 + encode_of_decode`. Grepping
  `openspec/changes/basen-rfc-conformance-theorems/` found **no** `encode_of_decode`
  or `bidir` mention. So the premise is inaccurate: no such divergence exists;
  tasks.md 4.3 describes `encodeB64Tail_of_rel`, which matches the code. (Flag: the
  premise was wrong, but the factual state — design and code agree on
  `encodeB64Tail_of_rel` — is fine.)
- **`nix flake check`**: read `/tmp/basen-flakecheck.log` — **green**:
  `✅ checks.aarch64-darwin.formatting`, `✅ checks.aarch64-darwin.lean`,
  `✅ packages.aarch64-darwin.native`. Date `Oct 25 16:05`. (Not re-run
  independently because a full Nix eval+build exceeds the foreground budget; the log
  is trusted as fresh and matches the commit set.)
- **`lake build` warning-free**: not re-run in foreground (>120s for full build;
  `/tmp/chk.lean` type-checked the module imports successfully, which entails a
  loaded olean — but not a fresh compile of changed files). The `tasks.md` claim
  "zero warnings" is unverified here; the `/tmp/chk.lean` run loaded existing
  oleans. Re-verify with a detached background run if warnings are load-bearing.
- **Empty-input `encodeB64 []`**: `#eval` failed with "depends on the `sorry` axiom"
  for `List.ofFn`-based repr of `Bytes 0` — this is a _tooling_ artifact (the
  `List.ofFn` `Bytes 0` `Repr` path pulls a stdlib axiom), not a proof defect; the
  roundtrip theorem `decodeFullB64_roundtrip []` type-checks.
  `decodeFullB64 (Bytes 0) = some []` evaluates to `some []` (verified). Single-byte
  and `Zg==` roundtrips eval correctly (`some [90,103,61,61]`), and `Zg==Zg==`
  rejects (`none`) — D8 works.
- **`openspec validate`**: `basen-rfc-conformance-theorems` → "valid";
  `lean-basen` → "valid". `openspec list --json`: three open changes. **Archive
  overlap:** `basen-rfc-conformance-theorems` only ADDED four _new_ requirement
  names ("A decoder rejects malformed input", "The encoder is canonical", "Decode is
  the unique canonical inverse", "The conformance laws are gated like the roundtrip
  laws") not present in the main spec (`openspec/specs/basen/spec.md` has only
  "Format codecs are `Codec` values" + "The `basen` bases are `Codec` values").
  `lean-basen` MODIFIES "The `basen` bases are `Codec` values" — the SAME requirement
  the rfc-conformance change's C3 requires modifying. **So archive of BOTH changes
  in any order will conflict**: `lean-basen` rewrites the requirement text, then
  `basen-rfc-conformance-theorems`'s C3 fix would rewrite it again (or the reverse),
  and archive's "MODIFIED must apply cleanly" will silently take one. This is the
  AGENTS "overlapping MODIFIED blocks break archive" hazard, and it is **live**:
  if C3 is fixed naively it creates exactly this overlap. Fix C3 by editing the
  _synced_ spec directly, or coordinate the two changes so the requirement text is
  edited once.

---

## Summary

Axiom discipline is genuinely clean (`[propext, Quot.sound]` uniformly; one even
`[propext]`) and no cheats exist. The _proofs_ are sound for the statements they
prove. The failures are in **statement fidelity and honesty**:

1. **The bench proves nothing about canonical output** — it repackages the ∃-theorem
   it is supposed to test, dropping the two RFC-relevant conjuncts (CRITICAL C1).
2. **Injectivity is stated weaker than the spec** (both-succeed rather than
   `Option`-equality), with no totality lemma to bridge (CRITICAL C2).
3. **Design D7 and the synced main spec are false** about the shape and about
   "unrepresentable"/"no per-format function" (CRITICAL C3 / HIGH H1).
4. **"Unique canonical inverse" / "total characterization" is not proved** — only
   converse + injectivity + specific rejection vectors (MEDIUM M3/M4).
5. Naming (`relB32Block_all_size3` proves 5), duplicated Common-eligible helpers,
   and a passing uppercase-only test labelled a "non-goal" (H2/H3/H4).

`nix flake check` is green; `openspec validate` is green for both changes, but the
`basen-rfc-conformance-theorems` task list marks 5.1/5.2 "DONE" on claims (byte-value
canonical vectors, "each rejection/canonical vector byte-for-byte") the code does not
support. Marks are **revisionist** on 5.1 and misleading on 5.2's "every new law"
(gate is manual, not automated).
