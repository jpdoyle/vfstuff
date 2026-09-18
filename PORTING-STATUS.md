# VeriFast proof-suite porting status

Target: the VeriFast checkout in `../verifast` (git master + local fixes, built
via its flake `packages.verifast`). Verify a single file with:

    ./vfcheck.sh <file.c>            # -shared -c, memory-scoped
    ./vfcheck.sh <file.c> <flags>    # e.g. pass -c only, or extra flags

## Root causes of the old-proof breakage (VeriFast 2022 -> 2025)

1. **C99 div/mod, uninterpreted in the SMT encoding.** `/` and `%` are now
   opaque function symbols with only the `div_rem`/`div_rem_nonneg`/
   `div_rem_nonneg_unique` facts (prelude.h). The old encoding used
   interpreted SMT div/mod, so z3 could distribute `d*K` products and
   substitute derived equalities into products on its own. Proofs that
   relied on that now need explicit lemma calls: `mul_distr`, `mul_subst`,
   `mul_subst_2` (added to mul.gh/mul.c), or `div_rem_nonneg_unique`.
2. **Type-exact chunk families.** `int32_t`, `uintptr_t`, `uint8_t` are now
   distinct types with their own pointsto families; `ints_`/`ullongs`/
   `uchars` etc. match `int*`/`unsigned long long*`/`unsigned char*` only.
3. **New pointer-provenance model.** `pointer_within_limits(field_ptr(...))`
   facts for `&x->field` arithmetic are no longer automatic; malloc blocks
   now provide `object_pointer_within_limits(p, size)`.
4. **Removed built-ins.** The old `euclid_div_sol` preset and
   `division_unique` built-in are gone (prelude.h now has `div_rem*`;
   this repo's div.gh still declares/proves its own `division_unique`).
5. **`vararg_int(size, value)`** gained a size argument; `vararg_double`
   variant added.
6. **Struct-array slices** (`s->arr[..n] |-> v`) are a new predicate family;
   `[f]`-fractional form works, but the chunks are the generic
   `integers_(void*, size, signed, count, vs)` family for typedef'd
   element types like int32_t.

## Passing (24 files, verified with vfcheck.sh)

core.c div.c mul.c poly.c bitops.c b64.c nats.c lists.c binsearch.c
isort.c termination.c test.c fingrp.c fulcrum.c euler1.c euler2.c ll.c
crypto/chacha20.c exercises/isort-exercises.c exercises/sort_exercises.c
lorg2/lorgint.c p25519/p25519.c p25519/p512m32p1.c p25519/p569_generated.c
(sorting.gh div.gh mul.gh numtheo.gh poly.gh and everything they guard).

## Still failing, with what each needs

| file | failure | fix needed |
|------|---------|------------|
| bcd.c | one `note_eq` before the loop invariant; needs `retv + pw_nat(10,n)*ret_digit + (new loop values + carry)*pw_nat(10,succ(n))` derived from the first note_eq through mul_distr/mul_subst_2 calls | route the rearrangement through lemma calls (z3 NLA can't) |
| numtheo.c | `ullongs(buff,_)` open in prime_sieve | port prime_sieve's buffer contract to the typed `ullongs`/`uintptrs` families or `unsigned long long*` buffers throughout (see ll-exercises note) |
| util.c | `u_llong_buffer_auto` body: `u_llong_integer_unique(start)` after `open ullongs` | same buffer-machinery port; the helpers live in util.gh and are used only by numtheo.c |
| euler3.c | prime_sieve requires `ullongs_(primes, ...)` chunks that malloc+sizeof(unsigned long long) produce, but the free/primes flow drops them | port the sieve buffer flow like mtest8.c pattern: `unsigned long long*` + `malloc(n*sizeof(unsigned long long))` |
| lorg/bi_big_int.c | `bi_block_disjoint`: `pointer_unique(&a->next)` no longer merges the two `big_int_block_next` field chunks | replace with merge_fractions/unique lemma on the new per-field family |
| lorg/bi_big_int_mul.c | FIXED (slice-indexed chunk write + mul_distr_sub_r). _plus.c: slice-indexed write fixes the bounds check but shifts failure to the outer-loop invariant (73) | `pointer_within_limits(ptr_add_(field_ptr(i,...), 0, int_typeid))` for field-element writes | the provenance-based pointer_within_limits fixpoint needs the malloc-range fact (object_pointer_within_limits(i, sizeof(big_int_block)) from malloc) carried through the bi_block predicate, or a helper lemma over malloc_block_big_int_block; numeric bounds (ints_limits2) do NOT imply it. NOTE: -fno-strict-aliasing -assume_no_subobject_provenance does NOT help (verified) — it's the range facts, not subobject provenance |
| lorg/bi_big_int_hex2.c | `chars_(s, cap, _)` chunk missing after the hex-buffer changes | same class |
| lorg2/lorgint-reduce.c | the first-loop invariant consumption now passes after mul_distr calls; next: `open ints(p,_)` at (74) — z3 can't prove `ptr_add_(start,n,int_typeid) == ptr_add_(p,1,int_typeid)` from `start+n == p` (the C-scaled pointer arithmetic vs the chunk keys) | restate the loop invariant's pointer equations in chunk-key form (or add the bridging assertion with the exact chunk keys) |
| finfield.c | DONE: Zp_times/Zp_is_zero fixed (mul_subst + mul_distr_sub_l/r, added to mul.gh). Remaining: primes_below_32's concrete {31,29,23,...} list | the all_no_divide/primality computations need explicit div_rem calls per check (uninterpreted % can't be computed by z3) |
| p25519/p25519_generated.c, p448_generated.c | finfield.gh(132) euclid_mod facts in generated proofs | same: the machine-generated proofs need per-division div_rem calls |
| cantbelieve_sort.c | `forall_elim(l, (count_matches)(l_old,l), cx)` at (121): the forall fact is for a differently-shaped list | re-establish `forall(l, (count_matches)(l_old,l))` for the appended list before the elim |
| lambda.c | union_variant/field_ptr chunk family | port to the new union-predicate shape |
| bigint.c | `pointer_within_limits(ptr_add(ret,1))` in hex_of_bytes caller | derive via malloc-block limits lemma |
| bigint/fibber.c | `chars_(x_hex, numbytes0, _)` chunk after the b64.h contract edits | update the caller to the new bytes_of_hex contract (`malloc_block(result, ?blk_len)`) |
| ll.c | FIXED: open the linked_list chunk in the loop body (produces the field_pointer_within_limits facts) + close in the else branch | done |
| hillelogram/leftpad.c, unique.c | PARTIALLY FIXED (chars_limits_auto now takes the provenance-form require). Remaining: the strcpy call needs `chars(ret+i, length(cs)+1, _)` (the init chars family); the pad loop's chunks are the uninit `chars_` family + repchar-valued `chars` slices — the loop invariant must be restated so the full buffer `ret[i..len+1]` is covered by the family strcpy consumes | restate the loop invariant over the init-chars family |
| va_args.c | `va_arg(ap,int)` needs the va_list args head `vararg_int(sizeof(int),k)`; the case fork on the head vararg happens but the chunk shape doesn't match | needs the loop's `varargs_ints`/`int_of_vararg` opens arranged so the head vararg is case-split before `va_arg` |
| exercises/ll-exercises.c | `Loop invariant required` | homework file (unsolved exercises); needs the student-style invariant, cf. ll.c list_length |
| mergesort.c | verifast-master arrays.gh ints_limits now requires `(uintptr_t)pxs <= ptr_provenance_max_addr(...)` (provenance-aware) and can't apply to the uninit `ints_` chunk of the malloc'd out buffer; plus a new `(li+ri) <= UINTPTR_MAX` overflow check on the merge loop index | port merge/merge_sort to the provenance-aware arrays.gh: derive the malloc-range facts (object_pointer_within_limits from malloc) and add `ln+rn <= UINTPTR_MAX` to merge's requires (caller proves it from the ints_limits pointer-range fact) |
| test.c (partially) | final `0xffffffff` value needs a nonlinear modulo step z3 4.15 won't do (see comment in file) | would need a truncate_unsigned uniqueness lemma routed through lemma calls |

## Packaging notes

- `../verifast` flake now exports `packages.verifast` (CLI verifier +
  crt/pkg manifests + stdlib sources). The Z3 ocaml-bindings META's bogus
  `zarith` requirement is stripped (it clashed with VeriFast's own `Z`
  module).
- `vfcheck.sh` runs one file under `systemd-run --user` memory limits.
