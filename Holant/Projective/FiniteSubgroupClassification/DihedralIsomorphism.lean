import Holant.Projective.FiniteSubgroupClassification.DihedralModels
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-! Group isomorphisms from the genuine abstract dihedral groups to the actual
displayed matrix subgroups. The finite matrix carriers are consequences of
the group constructions, not substitutes for them. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
noncomputable section

/-- The rotation character associated with the cyclic subgroup's canonical
`ZMod` parametrization. -/
def reflectedRotationHom (K : Subgroup (PGL2 ℂ)) [IsCyclic K] :
    Multiplicative (ZMod (Nat.card K)) →* PGL2 ℂ :=
  K.subtype.comp (zmodCyclicMulEquiv (inferInstance : IsCyclic K)).toMonoidHom

theorem reflectedRotationHom_injective (K : Subgroup (PGL2 ℂ)) [IsCyclic K] :
    Function.Injective (reflectedRotationHom K) :=
  Subtype.val_injective.comp (zmodCyclicMulEquiv (inferInstance : IsCyclic K)).injective

theorem reflectedRotationHom_mem (K : Subgroup (PGL2 ℂ)) [IsCyclic K]
    (i : Multiplicative (ZMod (Nat.card K))) : reflectedRotationHom K i ∈ K :=
  (zmodCyclicMulEquiv (inferInstance : IsCyclic K) i).property

/-- The abstract rotation/reflection formula as an actual projective homomorphism. -/
def reflectedDihedralHom (K : Subgroup (PGL2 ℂ)) [IsCyclic K]
    (hK : K ≤ diagonalTorus) : DihedralGroup (Nat.card K) →* PGL2 ℂ where
  toFun
    | .r i => reflectedRotationHom K (Multiplicative.ofAdd i)
    | .sr i => xClass * reflectedRotationHom K (Multiplicative.ofAdd i)
  map_one' := by change reflectedRotationHom K 1 = 1; exact map_one _
  map_mul' := by
    have hi (i : ZMod (Nat.card K)) : reflectedRotationHom K (Multiplicative.ofAdd i) ∈ diagonalTorus :=
      hK (reflectedRotationHom_mem K _)
    have hc (i j : ZMod (Nat.card K)) :
        Commute (reflectedRotationHom K (Multiplicative.ofAdd i))
          (reflectedRotationHom K (Multiplicative.ofAdd j)) :=
      (Commute.all _ _).map (reflectedRotationHom K)
    have hxx : xClass * xClass = 1 := by simpa only [pow_two] using xClass_square
    rintro (i | i) (j | j)
    · exact map_mul (reflectedRotationHom K) _ _
    · change xClass * reflectedRotationHom K (Multiplicative.ofAdd (j - i)) =
        reflectedRotationHom K (Multiplicative.ofAdd i) *
          (xClass * reflectedRotationHom K (Multiplicative.ofAdd j))
      simp only [ofAdd_sub, div_eq_mul_inv, map_mul, map_inv]
      symm
      calc
        _ = (reflectedRotationHom K (Multiplicative.ofAdd i) * xClass) *
            reflectedRotationHom K (Multiplicative.ofAdd j) := (mul_assoc _ _ _).symm
        _ = (xClass * (reflectedRotationHom K (Multiplicative.ofAdd i))⁻¹) *
            reflectedRotationHom K (Multiplicative.ofAdd j) := by rw [torus_mul_xClass (hi i)]
        _ = _ := by rw [mul_assoc, (hc i j).inv_left.eq]
    · change xClass * reflectedRotationHom K (Multiplicative.ofAdd (i + j)) =
        (xClass * reflectedRotationHom K (Multiplicative.ofAdd i)) *
          reflectedRotationHom K (Multiplicative.ofAdd j)
      simp only [ofAdd_add, map_mul, mul_assoc]
    · change reflectedRotationHom K (Multiplicative.ofAdd (j - i)) =
        (xClass * reflectedRotationHom K (Multiplicative.ofAdd i)) *
          (xClass * reflectedRotationHom K (Multiplicative.ofAdd j))
      simp only [ofAdd_sub, div_eq_mul_inv, map_mul, map_inv]
      rw [mul_assoc xClass, ← mul_assoc (reflectedRotationHom K _),
        torus_mul_xClass (hi i), ← mul_assoc, ← mul_assoc, hxx, one_mul, (hc i j).inv_left.eq]

/-- Every value of the homomorphism lies in the actual two-coset subgroup. -/
theorem reflectedDihedralHom_mem (K : Subgroup (PGL2 ℂ)) [IsCyclic K]
    (hK : K ≤ diagonalTorus) (g : DihedralGroup (Nat.card K)) :
    reflectedDihedralHom K hK g ∈ reflectedTorus K hK := by
  cases g with
  | r i => exact Or.inl (reflectedRotationHom_mem K _)
  | sr i => exact Or.inr ⟨_, reflectedRotationHom_mem K _, rfl⟩

/-- The actual subgroup is isomorphic to `D₂ₘ`, where `m` is its rotation order. -/
def reflectedDihedralEquiv (K : Subgroup (PGL2 ℂ)) [IsCyclic K]
    (hK : K ≤ diagonalTorus) :
    DihedralGroup (Nat.card K) ≃* reflectedTorus K hK :=
  MulEquiv.ofBijective ((reflectedDihedralHom K hK).codRestrict _
    (reflectedDihedralHom_mem K hK)) ⟨by
      rintro (i | i) (j | j) h
      all_goals have he := congrArg (fun z : reflectedTorus K hK => (z : PGL2 ℂ)) h
      · exact congrArg DihedralGroup.r
          (Multiplicative.ofAdd.injective (reflectedRotationHom_injective K he))
      · change reflectedRotationHom K (Multiplicative.ofAdd i) =
          xClass * reflectedRotationHom K (Multiplicative.ofAdd j) at he
        exact (reflection_not_mem_torus (hK (reflectedRotationHom_mem K (Multiplicative.ofAdd j)))
          (he ▸ hK (reflectedRotationHom_mem K (Multiplicative.ofAdd i)))).elim
      · change xClass * reflectedRotationHom K (Multiplicative.ofAdd i) =
          reflectedRotationHom K (Multiplicative.ofAdd j) at he
        exact (reflection_not_mem_torus (hK (reflectedRotationHom_mem K (Multiplicative.ofAdd i)))
          (he.symm ▸ hK (reflectedRotationHom_mem K (Multiplicative.ofAdd j)))).elim
      · exact congrArg DihedralGroup.sr
          (Multiplicative.ofAdd.injective (reflectedRotationHom_injective K (mul_left_cancel he))), by
      rintro ⟨q, hq | ⟨r, hr, rfl⟩⟩
      · obtain ⟨i, hi⟩ := (zmodCyclicMulEquiv (inferInstance : IsCyclic K)).surjective ⟨q, hq⟩
        exact ⟨.r i.toAdd, Subtype.ext (congrArg (fun z : K => (z : PGL2 ℂ)) hi)⟩
      · obtain ⟨i, hi⟩ := (zmodCyclicMulEquiv (inferInstance : IsCyclic K)).surjective ⟨r, hr⟩
        exact ⟨.sr i.toAdd, Subtype.ext (congrArg (fun z : K => xClass * (z : PGL2 ℂ)) hi)⟩⟩

/-- The source's standard matrix model has the genuine abstract dihedral type. -/
theorem dihedralModel_isomorphism {ω : ℂˣ} {m : ℕ} (hω : IsPrimitiveRoot ω m) :
    Nonempty (DihedralGroup m ≃* dihedralModel ω) := by
  have hc : Nat.card (cyclicModel ω) = m := (cyclicModel_card ω).trans hω.eq_orderOf.symm
  letI : IsCyclic (cyclicModel ω) := by
    change IsCyclic (Subgroup.zpowers (cyclicGenerator ω))
    infer_instance
  have e := reflectedDihedralEquiv (cyclicModel ω) (cyclicModel_le_torus ω)
  rw [← hc]
  exact ⟨e⟩

end
end Holant.Projective.FiniteSubgroupClassification
