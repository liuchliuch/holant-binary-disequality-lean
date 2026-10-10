import Holant.Proofs.Hardness.EOBinaryConjugateProgrammeBase
import Holant.Proofs.Hardness.EOBinaryPlaneConjugateNetwork

/-! The runtime paired-root list covers every nonzero marked network product,
and its physical answers are exactly the positive moments used by the filter.
No root distinctness, original-field conjugation closure, or oracle premise is
needed for these finite network identities. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeNetwork
open Holant Holant.Complexity
open scoped BigOperators
namespace B
export EOBinaryConjugateProgrammeBase (coefficients answers)
end B
namespace P
export EOBinaryConjugateProgrammePairs (roots roots_first roots_length)
end P
namespace R
export EOBinaryConjugateProgrammeRoots (roots_nonzero monomial_mem)
end R
namespace N
export EOBinaryPlaneConjugateNetwork (selected row marked base lift_spectrum power_value value)
end N
namespace I
export EOBinaryPlaneConjugate (spectrum monomial)
end I
namespace Q
export EOBinaryConjugateProgrammeQueries (Input moments positive_moments count)
end Q
set_option backward.isDefEq.respectTransparency false
variable {K L : Type} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L] [StarRing L]
variable (into : K→ₐ[ℚ]L) (f : Signature K 2)

omit [StarRing L] in
theorem coefficients_nonzero (hf : ∀z,f z≠0) : ∀j,B.coefficients into f j≠0 := by
  have h (z : Fin 2→Bool) : into (f z)≠0 := by
    intro hz
    apply hf z
    apply into.injective
    change into (f z)=into 0
    rw [hz,map_zero]
  intro j
  fin_cases j
  · exact h ![false,false]
  · exact h ![false,true]
  · exact h ![true,false]
  · exact h ![true,true]

/-- Every listed denominator anchor is nonzero when the original binary table
has full support; collisions between distinct multiplicity tuples are allowed. -/
theorem roots_nonzero (hf : ∀z,f z≠0) (n : ℕ) :
    ∀p∈P.roots (B.coefficients into f) n,p.1≠0 := by
  intro p hp
  have hm : p.1∈(P.roots (B.coefficients into f) n).map Prod.fst :=
    List.mem_map.mpr ⟨p,hp,rfl⟩
  rw [P.roots_first] at hm
  exact R.roots_nonzero (B.coefficients into f) (coefficients_nonzero into f hf) n _ hm

/-- Every nonzero marked value appears in the complete runtime root list. -/
theorem marked_mem (r : Q.Input) (a : Fin r.val.edges.length→Bool)
    (hn : into (N.marked f (N.selected r) (N.row r a))≠0) :
    into (N.marked f (N.selected r) (N.row r a))∈
      (P.roots (B.coefficients into f) r.val.vertices.length).map Prod.fst := by
  classical
  have hs := N.lift_spectrum into.toRingHom f (N.selected r) (N.row r a)
  change into (N.marked f (N.selected r) (N.row r a))∈
    I.spectrum into.toRingHom (EOBinaryPlaneConjugateQueries.coefficients f) r.val.vertices.length at hs
  rcases Finset.mem_insert.mp hs with hz|hs
  · exact False.elim (hn hz)
  · obtain ⟨powers,_,he⟩ := Finset.mem_image.mp hs
    rw [P.roots_first,←he]
    have hmap : into.toRingHom (I.monomial (EOBinaryPlaneConjugateQueries.coefficients f) powers)=
        I.monomial (B.coefficients into f) powers := by
      simp only [I.monomial,B.coefficients,map_prod,map_pow]
      rfl
    rw [hmap]
    exact R.monomial_mem (B.coefficients into f) r.val.vertices.length powers

/-- Exact interpreted list emitted by the original-field oracle batch and
then mapped into the named common field. Samples start at power one. -/
theorem answers_moments (r : Q.Input) : (B.answers f r).map into=
    (List.range (P.roots (B.coefficients into f) r.val.vertices.length).length).map
      (fun k=>∑a : Fin r.val.edges.length→Bool,
        into (N.base f r a)*into (N.marked f (N.selected r) (N.row r a))^(k+1)) := by
  have hstart : (B.answers f r).map into=Q.moments into f r := by
    simp only [B.answers,Q.moments,List.map_map,Function.comp_def]
  rw [hstart,Q.positive_moments,P.roots_length]
  change (List.range (Q.count r)).map _=(List.range (Q.count r)).map _
  apply List.map_congr_left
  intro k _
  change into (N.value f (fun z=>f z^(k+1)) r)=_
  rw [N.power_value f r (k+1) (Nat.zero_lt_succ k)]
  simp only [map_sum,map_mul,map_pow]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeNetwork
