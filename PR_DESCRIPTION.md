Halting proofs of two sibling BB(6) holdout machines (`Lemma halt : halts tm c0.`) via a shared 3-mode unary-run stack encoding, 3 symbolic pattern-repetition tokens, 3 accelerated Collatz-like rules, and checkpointed symbolic trajectories.

**Two files**, each with a top-level `Lemma halt : halts tm c0.` for its own string. Each imports only `Individual62` from busycoq (plus Coq standard library modules).

| machine                                     | `#` in 663 | file                                                                | mechanism                                                                                                                  |
| ------------------------------------------- | ---------: | ------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------- |
| `1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB---` |        230 | `verify/M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.v` (2,814 lines) | 3-mode (`BB` / `DL` / `CB`) unary-run stack + `STRepB1`/`STRep2`/`STRep12` tokens + Rules A/B/C (18 checkpoints, 203-bit halt) |
| `1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA` |        563 | `verify/M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.v` (2,723 lines) | 3-mode (`BB` / `DL` / `CB`) unary-run stack + `STRepB1`/`STRep2`/`STRep12` tokens + Rules A/B/C (6 checkpoints, 69-bit halt)  |

**Proof overview (`BB` / `DL` / `CB` unary-run stacks + symbolic tokens + Rules A/B/C + checkpointed trajectory).**

Holdouts `#230` and `#563` are near-siblings sharing 10 of 12 transitions under state renaming (`D`/`A`/`C`/`E`/`F`/`B` in `#230` play the roles of `B`/`C`/`D`/`A`/`E`/`F` in `#563`), differing only on two transitions (`C0` and `F0` in `#230`) that shift startup and elementary step counts. Both act on stacks of `0` separators and unary `1`-runs on both half-tapes and develop exponential-scale periodic run blocks before halting. Binary `N` values represent all run lengths and repetition counts (reaching 69-bit counters in `#563` and 203-bit counters in `#230`).

-   *Three-mode unary-run stacks (Sections 1–2).* Each half-tape encodes a stack of `MZero` (`0 >> ...`) and `MRun d` (`[1]^^(d + 1) *> (0 >> ...)`). Three head modes at the separator (`cfgBB L R` over `0`, `cfgCB L R` over `0`, and `cfgDL L R` moving left) obey 19 elementary transition rules and 2 `BB` helper reductions (`step_BB_*`, `step_DL_*`, `step_CB_*`) plus a `1`-run sweep loop (`cyc_R_A`, `exit_R_A`) and a halting step (`step_DL_zero_halt`).
    -   In `#230`, `cfgBB`, `cfgCB`, and `cfgDL` sit in states `D`, `A`, and `C` (with `cyc_R_A` in `E` and halt in `F` over `1`). `init_to_CB` takes 18 steps from `c0` to `cfgCB [] [MRun 1; MRun 0]`, and `runElemFast` runs `19,217` elementary stack steps to `initSymCyc3`.
    -   In `#563`, `cfgBB`, `cfgCB`, and `cfgDL` sit in states `B`, `C`, and `D` (with `cyc_R_A` in `A` and halt in `E` over `1`). `init_to_BB` takes 1 step from `c0` to `cfgBB [MRun 0] []`, and `runElemFast` runs `19,255` elementary stack steps to `initSymCyc3`.
-   *Symbolic pattern tokens and block sweeps (Sections 3–4).* Three repetition tokens compress long periodic blocks of runs identically in both machines: `STRepB1 k` (`[MRun 0; MRun 1]^k`), `STRep2 p` (`[MRun 1; MRun 0; MRun 1]^p` on the left / `[MRun 0; MRun 1; MRun 1]^p` on the right), and `STRep12 m` (`[MRun 1; MRun 0; MRun 1; MRun 0; MRun 1]^m` on the left / `[MRun 0; MRun 1; MRun 0; MRun 1; MRun 1]^m` on the right). Six bulk sweep lemmas (`sweep_BB_B1`, `sweep_BB_C2`, `sweep_BB_C12`, `sweep_CB_B1`, `sweep_CB_B2`, `sweep_CB_B12R`) and two total sweep functions (`sweepBB`, `sweepCB`) pass arbitrary repetitions across the head in one symbolic step, coalescing adjacent blocks via `eatFuel`.
-   *Pure unary simulator and accelerated Collatz-like Rules A, B, and C (Section 5).* To prove finite-step symbolic transitions cleanly by `reflexivity`, a pure unary token type `NatTok` and simulator `stepPure` mirror the elementary and block-sweep dynamics over `nat` (`stepPure_sound`), bridging back to `SymTok` (`N`) via `natTokToSym` and `symTokToNat`. Seven symbolic reduction lemmas (`test_ruleA0`, `test_ruleA_step`, `test_ruleC_step`, and the four separator variants `test_ruleB_AA`, `test_ruleB_AB`, `test_ruleB_BA`, `test_ruleB_BB` of 46–126 pure steps each) establish three iterated Collatz-like rules (`ruleA_iter`, `ruleB_iter`, `ruleC_iter`):
    -   *Rule A (`tryRuleA`):* consumes `6 * n` from a right-hand `MRun d` and `n` from `STRepB1 k` to produce `STRep12 (n - 1)` when `2 <= d / 6 <= k`.
    -   *Rule B (`tryRuleB`):* drains `STRep12 m` (`m >= 2`) and `m - 1` copies of `STRepB1 k` while adding `2 * (m - 1)` to `STRep2 p` and `4 * (m - 1)` to the right-hand run across any pair of separators `sep3A` / `sep3B` (using `splitB2` with fuel 32 in `#230` and 16 in `#563`).
    -   *Rule C (`tryRuleBC`):* drains `STRep2 p` (`p >= 3`) down to `STRep2 2` while adding `2 * (p - 2)` to both `STRepB1 k` and the right-hand run.
-   *Checkpointed trajectories to halt (Section 6).* The combined symbolic stepper `stepSym` (`stepSym_sound`) advances from `initSymCyc3` to the halting window via `4,096`-step `vm_compute` checkpoints (`stepSym4096`):
    -   *`#230` (`70,511` symbolic steps, 18 checkpoints):* `sym_chk1..sym_chk17` (`17 * 4,096` steps) plus `sym_chk18` (`879` steps) reach `symChk70511 = (HALT, STItem MZero :: ..., STItem (MRun 0) :: ...)` with `STRep12 2077426982857333580388655932463210634081595029892171852015193` and `STRepB1 10387134914286667901943279662316053170407975149460859260070043` (~203 bits). One final `step_DL_zero_halt` step enters halting state `F` over symbol `1` (`---`).
    -   *`#563` (`21,383` symbolic steps, 6 checkpoints):* `sym_chk1..sym_chk5` (`5 * 4,096` steps) plus `sym_chk6` (`903` steps) reach `symChk21383 = (HALT, STItem MZero :: ..., STItem (MRun 0) :: ...)` with `STRep12 68766212839422643803` and `STRepB1 343831064197113217107` (~69 bits). One final `step_DL_zero_halt` step enters halting state `E` over symbol `1` (`---`).

**Checked** on `BB6 @ 2733f61` with Coq 8.20.1. Against the pre-built `busycoq` framework (`verify/Individual62.vo`), each file compiles standalone in ~10–12 seconds and passes an external kernel check pinning all 12 cells of `tm = TM_from_str "<RLE>"`, `c0`, and `Print Assumptions`:

```sh
coqc -Q verify BusyCoq verify/M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.v
coqc -Q verify BusyCoq verify/M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.v
```

| file                                                     | `Print Assumptions halt`          |
| -------------------------------------------------------- | --------------------------------- |
| `verify/M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.v`   | `Closed under the global context` |
| `verify/M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.v`   | `Closed under the global context` |

**File names.** Each file is named `verify/M_<RLE>.v` with `---` written as `HHH` so the Coq module name starts with `M_` and contains no `-`. The exact RLE string with `---` is in `TM_from_str`. Happy to rename them if you prefer.

**AI disclosure:** These proofs were translated from Lean 4 and formalized in Rocq/Coq with AI assistance, and verified against unmodified `busycoq` (`Individual62.v`) with `coqc` and `Print Assumptions`. Extra verification and feedback are very welcome.
