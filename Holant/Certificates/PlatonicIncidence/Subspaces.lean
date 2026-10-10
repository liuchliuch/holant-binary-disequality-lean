import Holant.Certificates.PlatonicIncidence.DomainLines
import Holant.Certificates.RainbowOrbit.Proportional
import Mathlib.LinearAlgebra.Projectivization.Collinear

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev DomainPoint := Projectivization ℂ Mat

def domainPoint (g : PlatonicModel) (i : Fin (size g)) : DomainPoint :=
  Projectivization.mk ℂ (representative g i) (representative_ne_zero g i)

theorem domainPoint_injective (g : PlatonicModel) : Function.Injective (domainPoint g) := by
  intro i j h
  obtain ⟨c,_,hc⟩ := (proportional_point_iff _ _ _ _).mpr h
  exact projectively_injective g i j c hc

theorem pair_finrank (g : PlatonicModel) (i j : Fin (size g)) (hij : i≠j) :
    Module.finrank ℂ (Submodule.span ℂ ({representative g i,representative g j} : Set Mat))=2 := by
  have hli : LinearIndependent ℂ ![representative g i,representative g j] :=
    (Projectivization.independent_mk_iff_LinearIndependent _ _).mp
      ((Projectivization.independent_pair_iff_ne _ _).mpr
        (fun h => hij (domainPoint_injective g h)))
  rw [←Matrix.range_cons_cons_empty (representative g i) (representative g j) ![]]
  simpa using finrank_span_eq_card hli

/-- Any complex subspace of dimension at most two containing two different
source directions is their exact vector span. -/
theorem subspace_eq_pair (g : PlatonicModel) (W : Submodule ℂ Mat)
    (hW : Module.finrank ℂ W≤2) (i j : Fin (size g)) (hij : i≠j)
    (hi : representative g i∈W) (hj : representative g j∈W) :
    W=Submodule.span ℂ ({representative g i,representative g j} : Set Mat) := by
  have hle : Submodule.span ℂ ({representative g i,representative g j} : Set Mat)≤W := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with rfl|hx
    · exact hi
    · simpa only [Set.mem_singleton_iff] using hx ▸ hj
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [pair_finrank g i j hij]; exact hW)).symm

def deletion (g : PlatonicModel) (W : Submodule ℂ Mat) : Finset (Fin (size g)) := by
  classical
  exact Finset.univ.filter fun i => representative g i∈W

@[simp] theorem mem_deletion (g : PlatonicModel) (W : Submodule ℂ Mat) (i : Fin (size g)) :
    i∈deletion g W ↔ representative g i∈W := by
  classical
  simp [deletion]

theorem deletion_classification (g : PlatonicModel) (W : Submodule ℂ Mat)
    (hW : Module.finrank ℂ W≤2) :
    (deletion g W).card≤1 ∨ ∃t : Fin (secantCount g),deletion g W=globalLine g t := by
  classical
  by_cases h : (deletion g W).card≤1
  · exact Or.inl h
  · right
    obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (by omega : 1<(deletion g W).card)
    have he := subspace_eq_pair g W hW i j hij ((mem_deletion g W i).mp hi) ((mem_deletion g W j).mp hj)
    obtain ⟨t,ht⟩ := global_complete g i j hij
    refine ⟨t,Finset.ext (fun k => ?_)⟩
    rw [mem_deletion,he,←ht k]

def maximumLineSize : PlatonicModel → ℕ
  | .tetrahedral => 3
  | .octahedral => 4
  | .icosahedral => 5

theorem globalLine_bound (g : PlatonicModel) (t : Fin (secantCount g)) :
    2≤(globalLine g t).card ∧ (globalLine g t).card≤maximumLineSize g := by
  cases g
  · rcases tetrahedral_sizes t with h|h <;> simp [globalLine,maximumLineSize,h]
  · rcases octahedral_sizes t with h|h|h <;> simp [globalLine,maximumLineSize,h]
  · rcases icosahedral_sizes t with h|h|h <;> simp [globalLine,maximumLineSize,h]

theorem deletion_bound (g : PlatonicModel) (W : Submodule ℂ Mat)
    (hW : Module.finrank ℂ W≤2) : (deletion g W).card≤maximumLineSize g := by
  rcases deletion_classification g W hW with h|⟨t,ht⟩
  · exact h.trans (by cases g <;> decide)
  · rw [ht]
    exact (globalLine_bound g t).2

end
end Holant.Certificates.PlatonicIncidence
