# Simple symmetric 19-Venn diagrams (found 2026-09-20, 21:55-21:58 UTC; a fourth 2026-09-21 02:15 UTC, a fifth 03:41 UTC)

Five independent solutions, each a Z_19-invariant quadrangulation of the sphere by cube squares with all 2^19 = 524,288
labels present exactly once, i.e. the dual of a simple 19-fold rotationally symmetric Venn diagram (19 Jordan curves,
only double crossings, all 524,288 regions present and connected). Distinct as canonical face sets (symmetric
differences 25,460 / 233,966 / 230,242 of 524,286 faces among the first three; the fourth, s196001, differs from each of
them by 755,288 / 755,592 / 754,376 as unordered label-quadruple sets after 4.3 h of neutral drift at lambda 1.0; the fifth, s196007, differs from all four by 799,520-827,716).

| file | origin | sha256 (raw) |
|---|---|---|
| venn19-closure-s196002 | closure fleet venn-closure (c4-highcpu-24, europe-west1-b), seed 196002, T=0.25, lambda held 1.0, RW_UNLOCK=1, from source-s12-E38-M38D0.raw; ENERGY ZERO at t=12.9 s | fcb7ad34... |
| venn19-closure-s196004 | same VM, seed 196004; ENERGY ZERO at t=4.3 s | 285de8ea... |
| venn19-closure-s195001 | laptop (M4 Max), seed 195001, same recipe; ENERGY ZERO at t=190.2 s | a09ceae0... |
| venn19-closure-s196001 | same VM as s196002, seed 196001, same recipe; ENERGY ZERO at t=15545.0 s (4.3 h into the lambda 1.0 hold); pulled 2026-09-21 02:50Z and verified by both checkers plus the public verify.py (PASS, 67 s); pre-win E=38 M/D=19/19, missing 0x6e3b (rank 10), duplicate 0xe7b (rank 9, both copies degree 3), Hamming distance 3; closing move destroys one 0xe7b copy and creates 0x6e3b (last_move.py tags the tuple diff 'other') | 56e7e1a1... |
| venn19-closure-s196007 | same VM, seed 196007, lambda ramp 0.8->1.0 over 6 h (the l0.8-h6 arm), RW_UNLOCK=1; ENERGY ZERO at t=20783.2 s (lambda ~0.99); pulled 2026-09-21 03:50Z, verified by both checkers plus the public verify.py (PASS); pre-win E=38 M/D=19/19, missing 0xaf (rank 6), duplicate 0x22b (rank 5, both copies degree 3), Hamming distance 3, closed by the same degree-3-duplicate-into-hole move | 312e8c88... |

Closure VM venn-closure (24 seeds from the knot-free state, launched 21:55Z 2026-09-20) was stopped 04:15Z 2026-09-21 after its 6 h ramps: 4 of 24 seeds closed (s196002, s196004 at 4-13 s and s196001 at 4.3 h on the lambda 1.0 hold; s196007 at 5.8 h on the 0.8->1.0 ramp); at the stop, four more runs sat at E=76 with zero duplicates (s196003, s196013, s196015 and s196006 at E=114) and eleven at E<=190. Its strict/re-entry captures (70 files) remain on the persisted disk; logs in relaxed-walk/long19/fleet/collected/venn-closure/.

Full checksums: SHA256SUMS. Each solution comes with its exact pre-win state (`*-prewin.raw`, obtained by journal undo
of the winning move inside the engine), its progress log (`*.err`) and the faces JSON exported by the original engine.

## Verification transcript (run by claude, 2026-09-20 22:00 UTC, tools: relaxed-walk/long19/tools/verify_win.sh)

For each certificate:

1. Native reload with the ORIGINAL relaxed_walk5 (source sha 383d3692..., zero steps): checks that every face is a
   4-cycle of cube-square labels, Euler characteristic 2, twin structure, every vertex's darts form one rotation cycle,
   dart and label rotation symmetry, every curve a single cycle:

       start: V=524288 E(dges)=1048572 missing=0 dups=0 energy=0 strict=0
       start structure: OK

2. Independent Python checker (research/polar-calibration/gks-scaffold/gks_scaffold.check on
   interval_growth.oriented_faces of the exported faces; written on day one, shares no code with the walk), via
   relaxed-walk/cycle.py run_checker:

       ok true, V 524288, E 1048572, F 524286, euler 2, all_labels true, edge_multiplicities {2: 1048572}, bad_edges 0,
       face_sizes {4: 524286}, non_transversal_faces 0, vertices_single_rotation_cycle true,
       curves_two_sides_connected true, rotation_symmetric true, repeated_vertex_faces 0, venn_dual_valid true,
       all_crossings_transversal true

   Reports: verify-*-independent.json. Codex's independent validators: requested on the board (message 1070).

## Provenance chain (every state on disk, hashed)

1. `research/resolved-gks/gks19-quadrangulated-resolved.raw` (sha 760c73fb): Codex's resolved GKS19 scaffold, all
   labels present, 305,862 duplicate region instances.
2. `research/n19-endgame/e38-c9s5/source.raw` (sha c76f9afc): E=38 state from the cycle-driver lineage (2026-09-19),
   frozen: duplicate orbit 0x19 = {0,3,4} at instance degrees 6 and 7. Every 19 lineage stalled on this knot, which is
   inherited from the scaffold (0x19 is born there as a degree-18 giant plus a degree-4 twin).
3. `source-dissolved-E13984.raw` (sha 90421cac): 25 min at T=0.25, lambda held 0.35, RW_UNLOCK=1 with
   relaxed_walk5_capture19u (targeted proposals that land on a duplicate of degree > 3 attack its degree: RIII at a
   degree-3 neighbour or lens insertion on an incident edge; Metropolis rule unchanged). The 0x19 class is at
   multiplicity 1 on all 19 labels. E=13,984 (1,387 holes, 12,597 duplicates).
4. `source-s12-E38-M38D0.raw` (sha ffb0e1a7): sprint run s12, lambda 0.50 -> 1.0 over 3 h, unlock on, from state 3:
   E=38 in the (2n,0) form, missing orbits 0xbb5b and 0x199bd (both rank 11), zero duplicates, no crust knot.
5. Continuation from state 4 at T=0.25, lambda held 1.0, unlock on: 3 of the first 8 seeds reached E=0 within 4-190 s.

Method summary: the relaxed Metropolis walk that found the 17 (relaxed_walk5), given (a) the size-scaled budget it
never had at 19, and (b) one added proposal class that attacks high-degree duplicates, which is what dissolves the
crust knot the scaffold plants. Engine sources and hashes: relaxed-walk/long19/bin/, SHA256SUMS. Run records:
relaxed-walk/long19/{fleet/FLEET.md, probe/UNLOCK-TEST.md, sprint-states/, closure/}.
