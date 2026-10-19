Nonhalting proof of BB(6) holdout machine `#658` (`1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---`, `Lemma nonhalt : ~ halts tm c0.`), which acts as a DFA-guided call-stack transducer over word-level blocks `{V, K, Q}`. Unlike two-register transducers with an unstructured carry stack, this machine couples nine call-stream modes (`PA1`, `FA1`, `KA1`, `KHV`, `PHV`, `FH0`, `FH1`, `PH0`, `PH1`) to a 4-state right-to-left lookahead DFA (`S2`, `S3`, `S4`, `S5`) across 34 step rules (`R00`..`R33`).

**One file**, with a top-level `Lemma nonhalt : ~ halts tm c0.` for its string. It imports only `Individual62` from busycoq (plus Coq standard library modules).

| machine                                     | `#` in 663 | file                                                                 | tape & mechanism                                                              |
| ------------------------------------------- | ---------: | -------------------------------------------------------------------- | ----------------------------------------------------------------------------- |
| `1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---` |        658 | `verify/M_1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0REHHH.v` (2,620 lines) | left-tape; 9-mode, 4-state DFA-guided 34-rule call-stack transducer           |

**DFA-guided call-stack transducer (`Side` / `Seg` / `Mode` / `DState` / `StepRule` / `Scan` / `Good`).**

The proof lifts the low-level tape trajectory to a deterministic macro-step system `Step u u'` over words in `{V, K, Q_w}` and closes a five-piece inductive invariant `Good u` after ten startup rounds:

-   *Call-stack segments and turnaround (Section 1).* Four call symbols `ch`, `cb`, `cf`, and `ck` act on left half-tapes via `Side` and finite word segments `Seg`. Seventeen atomic `Seg` lemmas (`seg_cf_1`..`seg_ck_K`), 16 power/parity `Seg` lemmas (`seg_cf_keep`..`seg_ch_Qp_odd`) over `pairA = [cb; cf]` and `[ch]`, and 22 raw rule lemmas (`raw_PureA_V_dbl2`..`raw_CfH_Q_dbl1`) plus a 7-leg turnaround (`Side_turnaround` via `zP0`..`zP6`) characterize how call streams cross unprimed blocks `V_u = [1;1;0;0]`, `K_u = [0;0]`, `Q_u = [1;0]` and primed blocks `Vp = [0;1;1;0]`, `Kp = [0;0]`, `Qp = [0;1]`.
-   *Lookahead DFA, 34 step rules, and macro-steps (Section 2).* Words `u : list Word` map to configurations via `zCf (zTs u 0inf)`. Binary digit words `zDg A H u` encode `H`-bit numbers `A < 2^H` over `{K, Q_w}` (`Side_ch_default`). A 4-state right-to-left DFA `dfaRun u s` (`DState := S2 | S3 | S4 | S5`) tracks lookahead compatibility `modeMatches m s` for the nine call modes (`Mode := PA1..PH1`). Thirty-four rules (`StepRule := R00..R33`) with five counter updates (`dbl2`, `dbl1`, `keep`, `half0`, `half1`) compose into `Scan m1 s1 n1 u m2 s2 n2 v g`, yielding `Step_exec : Step u u' -> zCf (zTs u 0inf) -->+ zCf (zTs u' 0inf)` and `Rounds_exec`.
-   *Affine evaluator for concrete and symbolic scans (Section 3).* `evalAffineScan` runs a list of step rules against an affine input counter `mb * q + cb` (`evalAffineScan_sound`), and `checkStep` verifies concrete macro-steps by computation (`vm_compute`).
-   *Rational weight identities and DFA-guided survival (Section 4).* Rational summary functionals `z13` and `zW` (`QArith`) satisfy exact scaling `Scan_z13` (`psi m2 * z13 v * 2^g = psi m1 * z13 u`), counter drift bounds `Scan_delta`, and contraction `Scan_zW_contract`. A deterministic rule selector `pickRule m w s par` (`checkPickRule_all`) proves universal scan survival `Scan_survive` whenever `modeMatches m (dfaRun u s_end) = true` and `alpha m * zW u <= n - 2`. On `{K, Q_w}` digit blocks, `Scan_KQ_zW` bounds emitted weight by `kqA m s * 2^H + kqC m s`.
-   *Fixed segments and concrete orbit `init -> u_0 -> u_10` (Section 5).* `Scan_head` scans the 36-word prefix `head_w` from counter `3` to `b_head = 266862588`. `Scan_top` scans the 15-word top body `top_body` from any `b_top >= 2` to `64 * (b_top - 2) + 41`. `Scan_s_all` checks all `2 * 4 * 16 = 128` `(m_p, s_ds, bp mod 16)` cases across the 15-word bridge `s_full = s_base ++ bot_w` (`checkOneS_all`). From `c0`, 9 TM steps reach `zCf (zTs u_0 0inf)` with `u_0 = [V; Q_w]` (`init_to_u0`), followed by 10 certified rounds (`step_0`..`step_9`, `rounds_0_10`) to `u_10`.
-   *Five-piece invariant closure and non-halting (Section 6).* `Good u` splits `u` as `head_w ++ p_w ++ s_full ++ ds_core ++ top_base` with `p_w = V :: V :: p_tail`, `m >= 8`, `zDg A_core m ds_core`, `z13 p_w * 2^m = 2048`, and `zW p_w <= 43` (`good_u10` at `m = 62`). In `Good_step`, `Scan_survive` crosses `p_w` and `ds_core`, `Scan_s_all` bridges `s_full`, and `bound_b_end_zDg` pins the high bits of `n_end = 64 * (b_top - 2) + 41` to `A_top = 65151` while re-encoding the middle bits into a new digit core `ds_core'` of length `g_mid + 2`. `Good_step` closes `Step u u' /\ Good u'`, and `nonhalt` concludes `~ halts tm c0` via `multistep_nonhalt` and `progress_nonhalt_cond`.

**Checked** on `BB6 @ 2733f61` with Coq 8.20.1. Against the pre-built `busycoq` framework (`verify/Individual62.vo`), the file compiles standalone and passes an external kernel check pinning all 12 cells of `tm = TM_from_str "1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---"` and `Print Assumptions`:

```sh
coqc -Q verify BusyCoq verify/M_1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0REHHH.v
```

| file                                                     | `Print Assumptions nonhalt`       |
| -------------------------------------------------------- | --------------------------------- |
| `verify/M_1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0REHHH.v`   | `Closed under the global context` |

**File name.** The file is named `verify/M_<RLE>.v` with `---` written as `HHH` so the Coq module name starts with `M_` and contains no `-`. The exact RLE string is in `TM_from_str`. Happy to rename it if you prefer.

**AI disclosure:** This proof was translated from Lean 4 and formalized in Rocq/Coq with AI assistance, and verified against unmodified `busycoq` (`Individual62.v`) with `coqc` and `Print Assumptions`. Extra verification and feedback are very welcome.
