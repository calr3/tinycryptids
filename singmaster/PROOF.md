# The proof, in plain words

Everything is in `../lean/TinyCryptids/Singmaster/`. The main theorem is `halts_iff` in `Main.lean`,
for the 105-state design; `M77.lean` transfers it to the merged machine (`halts_iff_of_sim`).

## The arithmetic (`Spec.lean`)

* `prow n` is row `n` of Pascal's triangle, `(List.range (n + 1)).map (choose n)`.
  `pascal ys = y₀, y₀ + y₁, …, y_m` is the next row (`pascal_prow`), and rows are palindromes
  (`prow_reverse`, from `pascal_reverse`), so building the next row from the reversed row is fine.
* `tcnt N m` counts the positions `(n, k)`, `k ≤ n < m`, with `choose n k = N` (`tri m` lists them
  row by row; `tcnt_succ` adds a row).
* `row_self`: in row `N ≥ 2` only `k = 1` and `k = N − 1` hold `N` (for `2 ≤ k ≤ N − 2`,
  `choose N k ≥ 2(N − 1) > N` by Pascal's rule and `le_choose`).
* **`occ_iff`**: for `N ≥ 2` and `T ≥ 1`, `N` occurs at least `T + 2` times (a duplicate-free list
  of positions) iff `T ≤ tcnt N N`. Forward: positions in rows below `N` are at most `tcnt N N`
  (they lie in `tri N`, by `choose_range`), those in row `N` at most 2. Backward: add `(N, 1)` and
  `(N, N − 1)` (`choose_pred`). The machine uses `T = 7`.

## Tapes as lists (`Tape.lean`)

`cl q Lw Rw` is a configuration whose left half is the list `Lw` (nearest cell first) and whose
right half is `Rw`, both followed by blank; `cL q HL Rw` puts the head cell at the front of `HL`
(the two agree by definition, `cl_cL`). Single steps (`sr`, `sl`, `slc`), scans over runs of 1s or 0s
(`srn`, `sln`, `slz`), the gap-tolerant finders of `../Lychrel/Find.lean` (`fr_cross`,
`fl_cross`) and the four-zero walk (`w4_cross`) are restated on lists, with variants that take the
list equation to rewrite (`fl_crossE`, `srn'`, …). Trailing 0s are free (`cl_padR`, `cl_padL`).
The tactic `lfin` normalises both sides' lists and closes the goal by reflexivity.

## Comparing an entry with N (`Compare.lean`)

The tape is `C 0 N D E Y`: `C = Cw c` (hole at `c + 1`), `N = Nw a b` (hole at `a`), `D` the triangle
so far with E's separator (`DOK D`: what the finders need), `E` with a hole at `r`.

* `rnd D c e r a b Y` is a round in progress. `round`: if `r < e` and `a ≥ 2`, both cursors move
  (`r + 1`, `a − 1`). `rounds` iterates it from `r = 1, a = N`.
* `n_exh`: N's cursor exhausted while E's is not (E > N); `e_exh_lt`: E's exhausted with N's not at
  cell 1 (E < N); `e_exh_eq`: both at once, C += 1; `e_exh_halt`: the same with `c = 6`, the machine
  reaches `halt`. Each ends in `tail` (N's hole back to cell N, E's hole filled, to E's end).
* `cmp_ne`, `cmp_eq`, `cmp_halt` package these from `atE` (the head on E's cell 1) to `post`.

## The scan (`Scan.lean`)

The triangle is a list of items `(s, v)` (`s` 0s, then the block of `v`; `IOK`: `s ∈ {2, 3}`,
`v ≥ 1`), written by `itemsW`. `gc_fwd`, `gc_rev` give `DOK`. `cross` moves from one entry to the
next, `to_end` notices the end of the triangle (`endc`). **`scan`**: from the start of the items, if
the count `c + cntv N is ≤ 6` the machine reaches `endc` with that count, and if it is `≥ 7` it halts.

## The next row (`Gen.lean`)

The source row is read right to left; `g7 x Q P ws` is the start of source block `x` (processed
blocks `P`, the new row `rowW ws`), `spc` the return to the source cursor.

* `trans`: the first cell of a block writes `1 00 111` after the last 1 (the last block + 1, a new
  block of 1).
* `back_ok`: each further cell: back to the cursor, advance it, walk to the end, append `11`, move the
  last separator one cell right: the last two blocks grow by 1 (`rowW_snoc`, `rowW_succ`).
* `back_exh`, `y3_next`, `y3_done`: the block is done; the next block on the left, or the row is done.
* `block`: one source block `x` turns `ws₀ ++ [u]` into `ws₀ ++ [u + x, x]`. `gen_row` (induction on the
  blocks left of `x`): the new row is `pas u (x :: r)`, and `pascal_pas` identifies `pas 0` of the
  reversed row with `pascal`.
* `gen_start` (from `endc`, `qof_row` for the shape of the source row) and `gen_end` (N gets a cell
  on its left, C moves one cell left and its hole returns to cell 1; to the start of the next scan).

## The main theorem (`Main.lean`)

`Chk N` is the start of the scan for `N`, rows `0 … N − 1` on the tape (`triItems N`; `cnt_tri`:
`cntv N (triItems N) = tcnt N N`). `gen_all`: from the end of the scan to `Chk (N + 1)`, with
`pascal (prow (N − 1)) = prow N`. `cyc_ok`: `tcnt N N ≤ 6` gives `Chk N → Chk (N + 1)`;
`cyc_halt`: `tcnt N N ≥ 7` halts. `seed_reach`: the seed writes C, `N = 1` and row 0 and is at the end
of the triangle, so `gen_all 1` reaches `Chk 2`.

* (←) `haltAt_of`: take the least `N ≥ 2` with `tcnt N N ≥ 7` (`reach_k` reaches `Chk N`).
* (→) `not_halts_of`: if every `tcnt N N ≤ 6`, the configurations `Chk N` follow each other
  (`chk_ne` makes each step strict), so by `not_halts_of_progress` the machine never halts.

Both directions use `occ_iff` with `T = 7`.
