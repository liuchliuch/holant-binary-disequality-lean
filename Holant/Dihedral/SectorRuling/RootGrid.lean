import Holant.Dihedral.SectorRuling.FinitePencil

/-! The entire actual m-th root grid has exactly m algebraic phases. The finite
sample arguments do not assume a hand-picked set of three or four phases. -/
noncomputable section
namespace Holant.Dihedral.SectorRuling
open Holant Holant.Marked

abbrev Grid (m : ℕ) [NeZero m] := {z : ℂ // z ∈ Laurent.rootCoset m 1}

instance gridFintype (m : ℕ) [NeZero m] : Fintype (Grid m) := by
  classical
  infer_instance

theorem grid_card (m : ℕ) [NeZero m] : Fintype.card (Grid m)=m := by
  classical
  rw [Fintype.card_coe,Laurent.card_rootCoset]

private theorem grid_pow {m : ℕ} [NeZero m] (z : Grid m) : z.val^m=1 := by
  obtain ⟨u,hu⟩ := (Laurent.mem_rootCoset m 1 z.val).mp z.property
  have h := u.property
  rw [mem_rootsOfUnity] at h
  have hh := congrArg Units.val h
  have he : (u.val : ℂ)=z.val := by simpa using hu
  simpa only [Units.val_pow_eq_pow_val,Units.val_one,he] using hh

def gridValue {m : ℕ} [NeZero m] (z : Grid m) : Scalar :=
  Projective.CyclicPhasePencil.algebraicRoot (Nat.pos_of_ne_zero (NeZero.ne m)) z.val (grid_pow z)

theorem gridValue_roots {m : ℕ} [NeZero m] (z : Grid m) : Roots m (gridValue z) :=
  Projective.CyclicPhasePencil.algebraicRoot_pow _ _ _

theorem gridValue_injective {m : ℕ} [NeZero m] : Function.Injective (gridValue (m:=m)) := by
  intro z w h
  apply Subtype.ext
  exact congrArg (fun t : Scalar => (t:ℂ)) h

/-- Every source algebraic phase occurs in the actual complete finite grid. -/
theorem gridValue_surjective {m : ℕ} [NeZero m] (t : Scalar) (ht : Roots m t) :
    ∃ z : Grid m,gridValue z=t := by
  have hn : (t:ℂ) ≠ 0 := by exact_mod_cast ht.ne_zero (Nat.pos_of_ne_zero (NeZero.ne m))
  let u : ℂˣ := Units.mk0 (t:ℂ) hn
  have hu : u ∈ rootsOfUnity m ℂ := by
    rw [mem_rootsOfUnity]
    apply Units.ext
    change (t:ℂ)^m=1
    exact_mod_cast ht
  have hz : (t:ℂ) ∈ Laurent.rootCoset m 1 := by
    apply (Laurent.mem_rootCoset m 1 (t:ℂ)).mpr
    exact ⟨⟨u,hu⟩,by simp [u]⟩
  refine ⟨⟨(t:ℂ),hz⟩,?_⟩
  apply Subtype.ext
  rfl

end Holant.Dihedral.SectorRuling
