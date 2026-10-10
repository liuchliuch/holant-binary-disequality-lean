import Holant.Proofs.Closure.ClosureSixPortNormalSecond

/-! NEW UNVERIFIED closed C/C support normalization. Both actual C rulings
internally determine the normalization, the six residual-edge case and every
tag. No normalized support/atlas case is supplied to this producer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant ComplementarySector

/-- The eight-word four-flat coordinates are derived from both literal C
payloads with nonzero coefficients, in the SAME original six-port tensor. -/
theorem complementary_complementary_normal_support {m : ℕ} (h : Signature ℂ 6)
    (e : Equiv.Perm (Fin 6)) (D₀ : ComplementarySector m h e false)
    (D₁ : ComplementarySector m h e true) :
    ∃ edge : Fin 6, ∃ a b o : Bool, ∃ order : Equiv.Perm (Fin 6), ∃ flip : Word 6,
      ∀ w, h w ≠ 0 ↔ w ∈ (flatSupport edge a b o).image (gaugeWord order flip) := by
  let N := normalSecondPositions D₀ D₁
  have normalized (w : Word 6) :
      h (D₀.normalWord w) ≠ 0 ↔ w ∈ flatSupport N.edge N.fixedTag N.varyingTag N.orientationTag := by
    rw [flatSupport_partition,Finset.mem_union]
    by_cases even : w 1=w 0
    · have secondFalse : w ∉ secondFlatSupport N.edge N.fixedTag N.varyingTag N.orientationTag := by
        intro member
        have odd := ((secondFlat_support_iff _ _ _ _ w).mp member).1
        cases hw : w 0 <;> simp_all
      constructor
      · intro hn
        exact Or.inl ((normal_first_sector_support D₀ w even).mp hn)
      · rintro (first | second)
        · exact (normal_first_sector_support D₀ w even).mpr first
        · exact (secondFalse second).elim
    · have odd : w 1=!(w 0) := by cases h0 : w 0 <;> cases h1 : w 1 <;> simp_all
      have firstFalse : w ∉ firstFlatSupport := by
        intro member
        exact even ((firstFlat_support_iff w).mp member).1
      constructor
      · intro hn
        exact Or.inr ((normal_second_sector_support D₀ D₁ N w odd).mp hn)
      · rintro (first | second)
        · exact (firstFalse first).elim
        · exact (normal_second_sector_support D₀ D₁ N w odd).mpr second
  refine ⟨N.edge,N.fixedTag,N.varyingTag,N.orientationTag,D₀.normalOrder,D₀.normalFlip,?_⟩
  intro w
  obtain ⟨v,rfl⟩ := (gaugeWord D₀.normalOrder D₀.normalFlip).surjective w
  constructor
  · intro hn
    exact Finset.mem_image.mpr ⟨v,(normalized v).mp hn,rfl⟩
  · intro member
    obtain ⟨u,hu,equal⟩ := Finset.mem_image.mp member
    have same : u=v := (gaugeWord D₀.normalOrder D₀.normalFlip).injective equal
    subst u
    exact (normalized v).mpr hu

/-- The genuine C/C branch forces a literal zero sector of the ORIGINAL
signature. The contradiction uses an actual phase-one card with unique lifts. -/
theorem complementary_complementary_has_zero_sector {m : ℕ} (h : Signature ℂ 6)
    (deck : OrderedRootDeck m h) (e : Equiv.Perm (Fin 6))
    (D₀ : ComplementarySector m h e false) (D₁ : ComplementarySector m h e true) :
    ∃ order : Equiv.Perm (Fin 6), ∃ p : Bool, ZeroSector h order p := by
  obtain ⟨edge,a,b,o,order,flip,support⟩ := complementary_complementary_normal_support h e D₀ D₁
  exact gauge_four_flat_has_zero_sector h deck edge a b o order flip support

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
