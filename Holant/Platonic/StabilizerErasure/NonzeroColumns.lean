import Holant.Platonic.StabilizerErasure.BasisColumns

/-! A fixed computational output bit is correctable. Consequently an affine
basis-column encoding with no correctable port has no zero column functional.
This derives the source's m_r ≠ 0 condition rather than assuming it. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.Platonic.StabilizerLine
open scoped BigOperators ComplexConjugate
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

@[simp] theorem hermitian_ket_left (w : Word n) (f : Signature ℂ n) :
    hermitian (ket w) f=f w := by simp [hermitian,ket]

theorem hermitian_ext {f g : Signature ℂ n}
    (h : ∀v,hermitian v f=hermitian v g) : f=g := by
  ext w
  simpa using h (ket w)

theorem correctable_of_fixed_bit (V : StabilizerIsometry k (n+1)) (r : Fin (n+1))
    (b : Bool) (h : ∀f w,w r≠b → V.map f w=0) : Correctable V r := by
  intro R
  refine ⟨R b b,?_⟩
  intro f
  change V.adjoint (siteAction r R (V.map f))=R b b • f
  apply hermitian_ext
  intro g
  rw [←V.adjoint_identity]
  have he : hermitian (V.map g) (siteAction r R (V.map f))=
      R b b*hermitian (V.map g) (V.map f) := by
    simp only [hermitian,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : w r=b
    · have hv : siteAction r R (V.map f) w=R b b*V.map f w := by
        change (∑c : Bool,R (w r) c*V.map f (r.insertNth c (r.removeNth w)))=_
        rw [Finset.sum_eq_single b]
        · simp [←hw]
        · intro c _ hc
          rw [h f _ (by simpa using hc),mul_zero]
        · simp
      rw [hv]
      ring
    · simp [h g w hw]
  rw [he,V.isometry]
  simp [hermitian,Finset.mul_sum,mul_left_comm]

theorem ket_expansion (f : Signature ℂ n) : f=∑w : Word n,f w • ket w := by
  ext w
  simp [ket,eq_comm]

theorem zero_column_correctable (V : StabilizerIsometry k (n+1))
    (c : BinaryVector (n+1)) (M : BinaryVector k →ₗ[ZMod 2] BinaryVector (n+1))
    (a : BinaryVector k → ℂ)
    (h : ∀z,V.map (ket (wordVector z))=a z • ket (wordVector (c+M z)))
    (r : Fin (n+1)) (hz : ∀z,M z r=0) : Correctable V r := by
  apply correctable_of_fixed_bit V r (wordVector c r)
  intro f w hw
  conv_lhs => rw [ket_expansion f]
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_eq_zero
  intro u _
  have he := h (vectorWord u)
  simp only [word_vector] at he
  have hn : w≠wordVector (c+M (vectorWord u)) := by
    intro hwu
    apply hw
    rw [hwu]
    simp [wordVector,hz]
  simp [he,ket,hn]

theorem basis_columns_nonzero (V : StabilizerIsometry k (n+1))
    (c : BinaryVector (n+1)) (M : BinaryVector k →ₗ[ZMod 2] BinaryVector (n+1))
    (a : BinaryVector k → ℂ)
    (h : ∀z,V.map (ket (wordVector z))=a z • ket (wordVector (c+M z)))
    (hn : ∀r : Fin (n+1),¬Correctable V r) (r : Fin (n+1)) :
    (LinearMap.proj r).comp M≠0 := by
  intro hz
  apply hn r
  apply zero_column_correctable V c M a h r
  intro z
  simpa using LinearMap.congr_fun hz z

end
end Holant.Platonic.StabilizerErasure
