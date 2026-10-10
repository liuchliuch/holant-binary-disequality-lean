import Holant.Certificates.TetrahedralPreservers.RankOneClassification

/-! Exact cardinality of the projectivized rank-one preserver locus. -/
noncomputable section
namespace Holant.Certificates.TetrahedralPreservers
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

theorem outer_proportional_left {u v w z : V} (hv : v ≠ 0) {c : ℂ}
    (h : outer u v = c • outer w z) : ∃ d : ℂ, u = d • w := by
  obtain ⟨r,hr⟩ := pairing_nonzero hv
  have hh := congrArg (fun M : End => M *ᵥ r) h
  simp only [outer_apply,Matrix.smul_mulVec,smul_smul] at hh
  have hhh := congrArg (fun x : V => (pairing v r)⁻¹ • x) hh
  simp only [smul_smul,inv_mul_cancel₀ hr,one_smul] at hhh
  exact ⟨(pairing v r)⁻¹ * (c * pairing z r),hhh⟩

theorem outer_indices_unique (p : Fin 12 → V) (hn : ∀ i, p i ≠ 0)
    (hi : ∀ (i j : Fin 12) (c : ℂ), p i = c • p j → i=j)
    (a b : Fin 12 × Fin 12) (c : ℂ)
    (h : outer (p a.1) (p a.2) = c • outer (p b.1) (p b.2)) : a=b := by
  obtain ⟨d,hd⟩ := outer_proportional_left (hn a.2) h
  have hleft := hi a.1 b.1 d hd
  have hs := congrArg sharp h
  simp only [sharp_outer,sharp_smul] at hs
  obtain ⟨e,he⟩ := outer_proportional_left (hn a.1) hs
  exact Prod.ext hleft (hi a.2 b.2 e he)

/-- Projective classes of actual rank-one maps satisfying the two-sided predicate.
The existential formulation makes membership independent of a chosen representative. -/
def RankOneClass (S : Set V) := {p : Projectivization ℂ End //
  ∃ A : End, ∃ hn : A ≠ 0, A.rank = 1 ∧ TwoSided S A ∧ p = Projectivization.mk ℂ A hn}

def outerClass {S : Set V} (hS : Saturated S) (p : Fin 12 → V)
    (hn : ∀ i, p i ≠ 0) (hm : ∀ i, p i ∈ S) (ij : Fin 12 × Fin 12) : RankOneClass S :=
  ⟨Projectivization.mk ℂ (outer (p ij.1) (p ij.2)) (outer_ne_zero (hn _) (hn _)),
    _,outer_ne_zero (hn _) (hn _),rank_outer (hn _) (hn _),
    twoSided_outer hS (hm _) (hm _),rfl⟩

theorem outerClass_bijective {S : Set V} (hS : Saturated S) (p : Fin 12 → V)
    (hn : ∀ i, p i ≠ 0) (hm : ∀ i, p i ∈ S)
    (hi : ∀ (i j : Fin 12) (c : ℂ), p i = c • p j → i=j)
    (hc : ∀ A : End, A.rank = 1 → TwoSided S A →
      ∃ i j : Fin 12, ∃ c : ℂ, c ≠ 0 ∧ A = c • outer (p i) (p j)) :
    Function.Bijective (outerClass hS p hn hm) := by
  constructor
  · intro a b h
    have hh := congrArg Subtype.val h
    obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hh
    exact outer_indices_unique p hn hi a b c hc.symm
  · rintro ⟨q,A,hA,hr,hp,hq⟩
    obtain ⟨i,j,c,hc,he⟩ := hc A hr hp
    refine ⟨(i,j),Subtype.ext ?_⟩
    change Projectivization.mk ℂ (outer (p i) (p j)) _ = q
    rw [hq]
    symm
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨c,he.symm⟩

def externalRankOneEquiv : (Fin 12 × Fin 12) ≃ RankOneClass External :=
  Equiv.ofBijective (outerClass external_saturated externalPoint externalPoint_ne_zero externalPoint_mem)
    (outerClass_bijective external_saturated externalPoint externalPoint_ne_zero externalPoint_mem
      externalPoint_projectively_injective (fun A hA h => (external_rank_one_complete A hA).mp h))

def standardRankOneEquiv : (Fin 12 × Fin 12) ≃ RankOneClass Standard :=
  Equiv.ofBijective (outerClass standard_saturated standardPoint standardPoint_ne_zero standardPoint_mem)
    (outerClass_bijective standard_saturated standardPoint standardPoint_ne_zero standardPoint_mem
      standardPoint_projectively_injective (fun A hA h => (standard_rank_one_complete A hA).mp h))

/-- The source's 144 counts actual complex projective maps, not certificate rows. -/
theorem external_rank_one_count : Nat.card (RankOneClass External) = 144 := by
  rw [← Nat.card_congr externalRankOneEquiv]
  norm_num

theorem standard_rank_one_count : Nat.card (RankOneClass Standard) = 144 := by
  rw [← Nat.card_congr standardRankOneEquiv]
  norm_num

end Holant.Certificates.TetrahedralPreservers
