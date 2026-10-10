import Holant.Realization
import Holant.Complexity.BinaryInterpolation.CommonDenominator
import Holant.Complexity.FixedGadgetSubstitution.Partition
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Prefix


namespace Holant.LocalDrafts.BinaryInterpolation.RawPolynomial
open Holant.Complexity Holant.Complexity.BinaryInterpolation
open Holant.Complexity.FixedGadgetSubstitution
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] {s b : ℕ} {arity : ℕ → ℕ}

def marked (r : RawClosedNetwork) (label : ℕ) : Finset (Fin r.vertices.length) :=
  Finset.univ.filter (fun v => (r.vertices.get v).1 = label)

theorem marked_card (r : RawClosedNetwork) (label : ℕ) :
    (marked r label).card = occurrences label r := by
  classical
  have h := Compiler.indicator_sum label r.vertices
  rw [← List.ofFn_getElem_eq_map r.vertices
    (fun row : RawVertex => if row.1 = label then 1 else 0), List.sum_ofFn] at h
  simpa [marked, Finset.sum_ite, occurrences] using h

def pencil (G L R : (i : Fin s) → Signature K (arity i.val))
    (label : ℕ) (z : K) (i : Fin s) : Signature K (arity i.val) :=
  fun x => if i.val = label then L i x + z * R i x else G i x

def right (G R : (i : Fin s) → Signature K (arity i.val))
    (label : ℕ) (i : Fin s) : Signature K (arity i.val) :=
  fun x => if i.val = label then R i x else G i x

variable (r : RawClosedNetwork) (hr : r.WellFormed s b arity)
variable (G L R : (i : Fin s) → Signature K (arity i.val))
variable (kernels : Fin b → Bool → Bool → K) (label : ℕ)

def polynomial : Polynomial K :=
  networkPolynomial (r.realize hr G kernels) (marked r label)
    (fun v => L (r.signatureLabel hr v))
    (fun v => R (r.signatureLabel hr v)) Fin.elim0

theorem polynomial_eval (z : K) :
    (polynomial r hr G L R kernels label).eval z =
      (r.realize hr (pencil G L R label z) kernels).denote Fin.elim0 := by
  rw [polynomial, networkPolynomial_eval]
  apply congrFun (Network.denote_congr (r.shape hr) _ _ _ _ ?_ ?_) Fin.elim0
  · intro v x
    simp [pencilNetwork, RawClosedNetwork.realize, pencil, marked,
      RawClosedNetwork.signatureLabel]
  · intros; rfl

theorem polynomial_degree :
    (polynomial r hr G L R kernels label).natDegree ≤ occurrences label r := by
  rw [← marked_card r label]
  exact networkPolynomial_degree
    (r.realize hr G kernels) (marked r label)
    (fun v => L (r.signatureLabel hr v))
    (fun v => R (r.signatureLabel hr v)) Fin.elim0

theorem polynomial_top :
    (polynomial r hr G L R kernels label).coeff (occurrences label r) =
      (r.realize hr (right G R label) kernels).denote Fin.elim0 := by
  rw [← marked_card r label, polynomial, networkPolynomial_top_coefficient]
  apply congrFun (Network.denote_congr (r.shape hr) _ _ _ _ ?_ ?_) Fin.elim0
  · intro v x
    simp [rightNetwork, RawClosedNetwork.realize, right, marked,
      RawClosedNetwork.signatureLabel]
  · intros; rfl

/-- Boundary equality is a property of local records, not an extra source
signature or input promise. The signature equality retains ordered arguments. -/
theorem replacement_same_arity {targetCount : ℕ} {targetArity : ℕ → ℕ}
    (ts : ℕ → Template)
    (ht : ∀ i < s, (ts i).WellFormed targetCount b targetArity)
    (ha : sourceArity ts = arity)
    (T : (i : Fin targetCount) → Signature K (targetArity i.val))
    (c : K)
    (hlocal : ∀ i : Fin s,
      (⟨(ts i.val).boundary, ((ts i.val).network (ht i.val i.isLt) T kernels).denote⟩ :
        AnySignature K) = ⟨arity i.val, (if i.val = label then c else 1) • G i⟩) :
    ∃ hq : (replace ts r).WellFormed targetCount b targetArity,
      ((replace ts r).realize hq T kernels).denote Fin.elim0 =
        c ^ occurrences label r * (r.realize hr G kernels).denote Fin.elim0 := by
  subst arity
  refine ⟨query_wellFormed ts r hr ht, ?_⟩
  apply replacement_scale_power ts r hr ht G T kernels label c
  intro i
  exact eq_of_heq (Sigma.mk.inj_iff.mp (hlocal i)).2

/-- Explicit Lagrange recovery on the original raw graph, with its literal
serialized occurrence count; includes zero occurrences and zero values. -/
theorem recover (nodes : Fin (occurrences label r + 1) → K)
    (hnodes : Function.Injective nodes) :
    recoverTop nodes (fun i =>
      (r.realize hr (pencil G L R label (nodes i)) kernels).denote Fin.elim0) =
      (r.realize hr (right G R label) kernels).denote Fin.elim0 := by
  simp_rw [← polynomial_eval r hr G L R kernels label]
  rw [recoverTop_eq_coefficient nodes hnodes _
    (polynomial_degree r hr G L R kernels label), polynomial_top]

end
end Holant.LocalDrafts.BinaryInterpolation.RawPolynomial
