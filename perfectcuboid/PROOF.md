# The proof, in plain words

The Lean files are in `../lean/TinyCryptids/PerfectCuboid/` (namespace `TM.PerfectCuboid`).
Tapes are streams (`Core/Basic.lean`); a configuration `⟨q, L, R⟩` reads `R 0`, with `L` the
cells to its left, nearest first.

## Arithmetic (`Spec.lean`)

* The counter S is a pair `s = (k, j)` with `j ≤ 2k` (`Valid`), worth `val s = k * k + j`. One
  unit is `adv`: `j + 1`, or `(k + 1, 0)` after `j = 2k` (`val_adv`: one more). `advN n` is `n` units
  (`val_advN`, `advN_add`). `sq_iff`: `val s` is a square iff `j = 0`.
* A block of `L` cells stands for `v L = L / 2 - 1`.
* `Good (x, y, z)`: the four sums of squares of `v x, v y, v z` are squares. `good_of_cuboid` and
  `cuboid_of_good` relate it to the statement (edges `2a + 2, 2b + 2, 2c + 2`).
* `nxt` is the search order; `reached`: every triple of lengths `≥ 4` is `itr k seedT` for some
  `k` (well-founded on the total, then C, then B, as for Fermat's NEXCOM).

## A block (`Proc.lean`)

* `Ev` lists (zeros in pairs) are what the parsers cross (`crossR`, `crossL`, `findR`, `findL`).
* `Sb s` is S on the tape. `sadv`: from the cell after S's hole (where the right parser stops),
  S's step, back on S's leading 1 in `PL1`. `trip`: from the block, to S, the step, back to
  the block's hole `h` in `hA`.
* `Xw a r t` is the block during processing: `a` ones, `m`, the spacer, the region of `2r + 1`
  cells with `h` on region cell `t`; `XE L` the block with only `h` left. One unit:
  `u_step` (`h` moves on), `u_wrap` (`h` home, back to the region's first cell), `u_wrap0` and
  `u_last` (`h` arrives home: `grow`, `m` two cells left or no region left).
* `region`: one region, `2r + 1` units; `regions`: all of them, `U a r` units, with `U_eq`
  (`U a r + r² = (r + 1 + (a - 1) / 2)²`) and `U_v`. `block`: a set-up block of `L ≥ 4` cells adds
  `v L * v L` units and ends on the first cell after its right separator (`xe_done`).

## The check and the window counter (`Check.lean`)

* G is `gapL W`: `[F, F] ++ gm W ++ [F, F]`.
* `cktick`: S's hole home: W ticks (`tk`), S reset to `(0, 0)` when it wraps (`reset`), and back
  to the block's `h` (`pl_ret`).
* `ckabort`: S's hole not home: the hole goes home, G becomes `gapL 2`, and the head is left of G
  in `q1`.

## The queue (`Step.lean`, `Queue.lean`, `Tuple.lean`)

* `init_real`, `init_Z`: setting up a block. `step_real`, `step_Z`: set up, check passes,
  process.
* `qL t` is the queue; `TS t s` the start of a tuple (`n5` on A's first cell, W = 2, S home).
* `home`, `wrap`: from the end of the queue home to A (`wcross` over `Clean` lists).
* `Cl l l'`: the scan after an abort turns `l` (read leftwards, with holes) into `l'`;
  `clscan`, `clean_home` (it ends on A's first cell in NEXCOM's `ea0`).
* `Tuple.lean`: the positions `PA`, `PB`, `PC`, `PZ` (`n5` on A, B, C, Z) and `PE` (after Z);
  `stepA`, `stepB`, `stepC`, `stepZ`, `endA` (wrap), `endH` (W = 2: halt); the aborts `abB`,
  `abC`, `abZ` (with `Cl.mark` for the block in hand), via `abort_end`.

## The search (`Enum.lean`, `Main.lean`)

* `nex1`, `nex2`, `nex3`, `nexcom`: NEXCOM on the tape, ending at `TS (nxt t) s`.
* `boot`: from the blank tape to `TS (4, 4, 4) (0, 0)` (seed, abort routine, the scan finding no
  queue, the chain `zc`).
* `tuple`: from `TS t s`: with `σ n = advN n (0, 0)` the twelve checks see `σ` of 0, `a²`,
  `a² + b²`, `a² + b² + c²`, 0, `a²`, `a² + b²`, `c²`, `c²`, `c² + a²`, `b²`, `b² + c²`. If `Good t`
  the machine halts (`HaltAt`); otherwise the first failing check aborts and the machine
  reaches `TS (nxt t) s'` in at least one step.
* `halts_iff`: (→) if no perfect cuboid exists, no tuple is `Good`, so `TS` configurations
  always progress to another one (`not_halts_of_progress`) and the machine never halts after
  `boot`; (←) `haltAt_of`: the cuboid's tuple is reached (`reached`, `search`) unless the machine
  halted before, and there it halts.
* `M88.lean` (generated): the merged machine simulates the design (`compat`), so
  `halts_iff_of_sim` transfers the theorem.
