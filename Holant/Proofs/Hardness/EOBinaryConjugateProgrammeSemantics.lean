import Holant.Proofs.Hardness.EOBinaryConjugateProgrammeSemanticsRounds
import Holant.Proofs.Hardness.EOBinaryConjugateProgrammeExecution

/-! End-to-end collision-tolerant semantics of the concrete finite controller.
The queried moments are positive, repeated roots need no deduplication, and
all denominators are proved nonzero from the actual root list. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeSemantics
open scoped BigOperators
set_option maxRecDepth 32768
set_option Elab.async false
variable {L : Type} [Field L] [CharZero L]

/-- Padding the finite loop after all requested passes leaves a genuine fixed point. -/
theorem initial_stable (roots : List (L×L)) (values : ℕ→L)
    (hr : ∀p∈roots,p.1≠0) (rounds : ℕ)
    (hrounds : roots.length*(roots.length+1)≤rounds) :
    let final := S.step^[rounds] (S.initial roots (V.table roots.length values))
    final.pending=[] ∧ final.divisor≠0 ∧
      final.numerator/final.divisor=(roots.map (contribution roots values)).sum := by
  let q := roots.length*(roots.length+1)
  let start := S.initial roots (V.table roots.length values)
  have he := outer_exact roots values hr roots (fun _ h=>h) 0 1 (one_ne_zero : (1:L)≠0) q
  change let final := S.step^[q] start; _ at he
  dsimp only at he ⊢
  simp only [zero_div,zero_add] at he
  have hp : ((S.step^[q]) start).pending=[] := he.1
  have hf : S.step ((S.step^[q]) start)=(S.step^[q]) start := by
    simp [S.step,hp]
  have hn : rounds=(rounds-q)+q := by dsimp [q]; omega
  change (S.step^[rounds] start).pending=[] ∧ _
  rw [hn,Function.iterate_add_apply,Function.iterate_fixed hf]
  exact he

variable [StarRing L]

omit [CharZero L] in
/-- Paired roots produced by the controller give exactly the algebraic filter sum. -/
theorem contributions_eq (roots : List (L×L)) (values : ℕ→L)
    (hc : ∀p∈roots,p.2=star p.1) :
    (roots.map (contribution roots values)).sum=A.result (roots.map Prod.fst) values := by
  unfold A.result
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  simp [contribution,weighted,factor,A.term,hc p hp]

/-- Exact reconstruction for arbitrary finite coefficients and collision-prone modes. -/
theorem reconstruct {I : Type*} [Fintype I]
    (roots : List (L×L)) (c w : I→L)
    (hr : ∀p∈roots,p.1≠0) (hc : ∀p∈roots,p.2=star p.1)
    (hw : ∀i,w i≠0→w i∈roots.map Prod.fst)
    (rounds : ℕ) (hrounds : roots.length*(roots.length+1)≤rounds) :
    let moments := (List.range roots.length).map fun k=>∑i,c i*w i^(k+1)
    let final := S.step^[rounds] (S.initial roots moments)
    final.pending=[] ∧ final.divisor≠0 ∧
      final.numerator/final.divisor=∑i,c i*star (w i) := by
  have h := initial_stable roots (fun k=>∑i,c i*w i^(k+1)) hr rounds hrounds
  rw [table_eq_range] at h
  dsimp only at h ⊢
  refine ⟨h.1,h.2.1,h.2.2.trans ?_⟩
  rw [contributions_eq roots _ hc]
  apply EOBinaryConjugateProgrammeFilter.result_eq _ c w _ hw
  intro r hmem
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hmem
  exact hr p hp

/-- The physical iterator's own encoded fuel supplies every required scan round. -/
theorem physical_reconstruct [Algebra ℚ L] {d : ℕ} (F : Holant.Algebraic.FixedField L d)
    {I : Type*} [Fintype I] (roots : List (L×L)) (c w : I→L)
    (hr : ∀p∈roots,p.1≠0) (hc : ∀p∈roots,p.2=star p.1)
    (hw : ∀i,w i≠0→w i∈roots.map Prod.fst) :
    EOBinaryConjugateProgrammeLoop.result F
      (S.initial roots ((List.range roots.length).map fun k=>∑i,c i*w i^(k+1)))=
        ∑i,c i*star (w i) := by
  let moments := (List.range roots.length).map fun k=>∑i,c i*w i^(k+1)
  let start := S.initial roots moments
  have hfuel := (EOBinaryConjugateProgrammeWidth.counts_le_bytes F start).2.2
  have h := reconstruct roots c w hr hc hw
    ((EOBinaryConjugateProgrammeState.encoding F).encode start).length hfuel
  exact h.2.2

/-- Original-field answers are transported only after evaluation. The original
field K carries no star operation or conjugation-closure hypothesis. -/
theorem physical_embedded_reconstruct [Algebra ℚ L] {d : ℕ}
    (F : Holant.Algebraic.FixedField L d) {K : Type*} [Field K] [Algebra ℚ K]
    (into : K→ₐ[ℚ] L) {I : Type*} [Fintype I]
    (roots : List (L×L)) (c w : I→K)
    (hr : ∀p∈roots,p.1≠0) (hc : ∀p∈roots,p.2=star p.1)
    (hw : ∀i,into (w i)≠0→into (w i)∈roots.map Prod.fst) :
    EOBinaryConjugateProgrammeLoop.result F
      (S.initial roots ((List.range roots.length).map fun k=>into (∑i,c i*w i^(k+1))))=
        ∑i,into (c i)*star (into (w i)) := by
  simpa only [map_sum,map_mul,map_pow] using
    physical_reconstruct F roots (fun i=>into (c i)) (fun i=>into (w i)) hr hc hw

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeSemantics
