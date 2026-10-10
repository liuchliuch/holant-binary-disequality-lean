import Holant.Certificates.TetrahedralPreservers.RankDeficient
import Holant.Certificates.TetrahedralPreservers.Zero

/-! Source Proposition 9.27 and the tetrahedral row of Proposition A.25.
Counts are of actual complex projective linear maps; reconstruction uses the
original bilinear Frobenius dual and literal ordered four-port coefficients. -/
noncomputable section
namespace Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence
set_option backward.isDefEq.respectTransparency false

open Holant.Certificates.OctahedralSeparator in
/-- The exact square used in the source's normalizer calculation, including
its nonzero projective scale. -/
theorem sourceR_square_literal :
    sourceR*sourceR=(2*((Real.sqrt 2 : ℂ)-1)) • (Matrix.of Q0+Matrix.of Q1) ∧
      (2*((Real.sqrt 2 : ℂ)-1) : ℂ) ≠ 0 := by
  have hraw : mm sourceRRaw sourceRRaw = ms (rat 2*(root-1)) (q 0+q 1) := by
    decide +kernel
  have hscale : embed (rat 2*(root-1))=2*((Real.sqrt 2 : ℂ)-1) := by
    norm_num [embed_mul,embed_sub,rat,root,embed_coeff,embed_one,rootTwo]
  constructor
  · change complexMatrix sourceRRaw*complexMatrix sourceRRaw = _
    rw [← complexMatrix_mm,hraw,complexMatrix_ms,hscale,complexMatrix_add]
    simp [complexMatrix_q,quaternionBasis]
  · rw [← hscale]
    exact embed_ne_zero (by decide +kernel : rat 2*(root-1) ≠ 0)

/-- The rank-r locus in the projectivization of the actual endomorphism space. -/
def ProjectiveRankClass (S : Set V) (r : ℕ) := {p : Projectivization ℂ End //
  ∃ A : End, ∃ hn : A ≠ 0, A.rank=r ∧ TwoSided S A ∧ p=Projectivization.mk ℂ A hn}

theorem projectiveRankClass_empty {S : Set V} {r : ℕ}
    (h : ∀ A : End, TwoSided S A → A.rank ≠ r) : Nat.card (ProjectiveRankClass S r)=0 := by
  letI : IsEmpty (ProjectiveRankClass S r) := ⟨by
    rintro ⟨p,A,hn,hr,hp,he⟩
    exact h A hp hr⟩
  simp

theorem standard_rank_distribution :
    Nat.card (ZeroPreserver Standard)=1 ∧
    Nat.card (ProjectiveRankClass Standard 1)=144 ∧
    Nat.card (ProjectiveRankClass Standard 2)=0 ∧
    Nat.card (ProjectiveRankClass Standard 3)=0 ∧
    Nat.card (ProjectiveRankClass Standard 4)=576 :=
  ⟨zero_preserver_count Standard,standard_rank_one_count,
    projectiveRankClass_empty no_standard_rank_two,
    projectiveRankClass_empty no_standard_rank_three,standard_rank_four_count⟩

/-- The source's complete 1,144,0,0,576 rank distribution. -/
theorem external_rank_distribution :
    Nat.card (ZeroPreserver External)=1 ∧
    Nat.card (ProjectiveRankClass External 1)=144 ∧
    Nat.card (ProjectiveRankClass External 2)=0 ∧
    Nat.card (ProjectiveRankClass External 3)=0 ∧
    Nat.card (ProjectiveRankClass External 4)=576 :=
  ⟨external_zero_count,external_rank_one_count,
    projectiveRankClass_empty no_external_rank_two,
    projectiveRankClass_empty no_external_rank_three,external_rank_four_count⟩

theorem external_possible_ranks (A : End) (h : TwoSided External A) :
    A=0 ∨ A.rank=1 ∨ A.rank=4 := by
  have hle : A.rank ≤ 4 := by simpa using Matrix.rank_le_width A
  have h2 := no_external_rank_two A h
  have h3 := no_external_rank_three A h
  have hr : A.rank=0 ∨ A.rank=1 ∨ A.rank=4 := by omega
  rcases hr with hr | hr
  · exact Or.inl ((rank_zero_iff A).mp hr)
  · exact Or.inr hr

theorem external_rank_one_reconstruction (A : End) (hA : A.rank=1) (h : TwoSided External A) :
    ∃ U W : BinaryMatrix, U.det ≠ 0 ∧ W.det ≠ 0 ∧
      reconstruct A=(2 : ℂ)⁻¹ • P0 U W := by
  obtain ⟨u,v,hu,hv,rfl⟩ := (rank_one_twoSided_iff external_saturated external_detects A hA).mp h
  refine ⟨assemble v,assemble u,?_,?_,reconstruct_outer u v⟩
  · apply RainbowOrbit.External.Direction.det_ne_zero
    exact (mem_coefficientSet_iff _ v).mp hv
  · apply RainbowOrbit.External.Direction.det_ne_zero
    exact (mem_coefficientSet_iff _ u).mp hu

/-- Every nonzero external preserver reconstructs an actual product on one
of the three original binary-pair matchings, with nonzero scalar and
nonsingular factors. This is an analytic tensor identity. -/
theorem external_binary_pair_reconstruction (A : End) (h : TwoSided External A) (hA : A ≠ 0) :
    ∃ r : Fin 3, ∃ U W : BinaryMatrix, ∃ c : ℂ,
      U.det ≠ 0 ∧ W.det ≠ 0 ∧ c ≠ 0 ∧ reconstruct A=c • matchingProduct r U W := by
  rcases (external_possible_ranks A h).resolve_left hA with hr | hr
  · obtain ⟨U,W,hU,hW,he⟩ := external_rank_one_reconstruction A hr h
    exact ⟨0,U,W,(2 : ℂ)⁻¹,hU,hW,by norm_num,he⟩
  · obtain ⟨U,W,hU,hW,he | he⟩ := external_rank_four_reconstruction A hr h
    · exact ⟨1,U,W,1,hU,hW,one_ne_zero,by simpa [matchingProduct] using he⟩
    · exact ⟨2,U,W,1,hU,hW,one_ne_zero,by simpa [matchingProduct] using he⟩

/-- The same statement applied to a literal original four-port tensor. -/
theorem original_tensor_factorization (f : FourTensor) (h : TwoSided External (cardMatrix f))
    (hf : f ≠ 0) : ∃ r : Fin 3, ∃ U W : BinaryMatrix, ∃ c : ℂ,
      U.det ≠ 0 ∧ W.det ≠ 0 ∧ c ≠ 0 ∧ f=c • matchingProduct r U W := by
  have hn : cardMatrix f ≠ 0 := by
    intro hz
    apply hf
    have hh := reconstruct_cardMatrix f
    rw [hz] at hh
    have hr : reconstruct 0=0 := by
      ext x
      simp [reconstruct,assemble]
    exact hh.symm.trans hr
  obtain ⟨r,U,W,c,hU,hW,hc,he⟩ := external_binary_pair_reconstruction (cardMatrix f) h hn
  exact ⟨r,U,W,c,hU,hW,hc,by simpa only [reconstruct_cardMatrix] using he⟩

/-- Source Proposition 9.27: representative independence, exact projective
rank counts, and the original Frobenius binary-pair factorization. -/
theorem external_tetrahedral_two_sided_preservers :
    (∀ A : End, ∀ r : V, ∀ c : ℂ, ∀ _hc : c ≠ 0,
      ((A.mulVec (c • r)=0 ∨ A.mulVec (c • r) ∈ External) ∧
       ((sharp A).mulVec (c • r)=0 ∨ (sharp A).mulVec (c • r) ∈ External)) ↔
      ((A.mulVec r=0 ∨ A.mulVec r ∈ External) ∧
       ((sharp A).mulVec r=0 ∨ (sharp A).mulVec r ∈ External))) ∧
    (Nat.card (ZeroPreserver External)=1 ∧
      Nat.card (ProjectiveRankClass External 1)=144 ∧
      Nat.card (ProjectiveRankClass External 2)=0 ∧
      Nat.card (ProjectiveRankClass External 3)=0 ∧
      Nat.card (ProjectiveRankClass External 4)=576) ∧
    (∀ A : End, TwoSided External A → A ≠ 0 →
      ∃ r : Fin 3, ∃ U W : BinaryMatrix, ∃ c : ℂ,
        U.det ≠ 0 ∧ W.det ≠ 0 ∧ c ≠ 0 ∧ reconstruct A=c • matchingProduct r U W) :=
  ⟨fun A r c hc => twoSided_representative_independent external_saturated A r hc,
    external_rank_distribution,external_binary_pair_reconstruction⟩

end Holant.Certificates.TetrahedralPreservers
