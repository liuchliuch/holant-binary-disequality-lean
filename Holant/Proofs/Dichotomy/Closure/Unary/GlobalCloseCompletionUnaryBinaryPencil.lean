import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBinarySpectrum

/-! Exact positive powers of the actual two-sided binary endpoint. The
perpendicular rank-one projector is the constant term of the reversed
spectral pencil; no inverse binary is used as a physical graph. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBinaryPencil
open Holant Holant.Tractable
open Holant.Certificates.MatchingContractionClosure
namespace S
export GlobalCloseCompletionUnaryBinarySpectrum (projector projector_mul projector_sum binary_decomposition)
end S
namespace U
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddNonisotropicFrame (norm chart)
end U
namespace E
export GlobalCloseCompletionUnaryHigherEq4 (endpoint)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {K : Type} [Field K]

theorem power_split (C D : Binary (K:=K)) (hCC : C*C=C) (hDD : D*D=D)
    (hCD : C*D=0) (hDC : D*C=0) (hsum : C+D=1) (a b : K) (k : ℕ) :
    (a • C+b • D)^k=a^k • C+b^k • D := by
  induction k with
  | zero => simpa only [pow_zero,one_smul] using hsum.symm
  | succ k ih =>
    rw [pow_succ,ih]
    simp only [Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
      hCC,hDD,hCD,hDC,smul_zero,zero_add,add_zero,pow_succ]
    simp only [mul_comm]

theorem pencil (u : Signature K 1) (hu : U.norm u≠0) (f : Signature K 2)
    (A B : K) (hb : B≠0) (form : U.chart u f=E.endpoint 2 A B) (k : ℕ) :
    (Holant.LocalDrafts.FinitePGL2.Stabilization.binaryMatrix f)^k=
      (B/U.norm u)^k • (S.projector u true+(A/B)^k • S.projector u false) := by
  rw [S.binary_decomposition u hu f A B form]
  rw [power_split _ _ (by simpa using S.projector_mul u hu false false)
    (by simpa using S.projector_mul u hu true true)
    (by simpa using S.projector_mul u hu false true)
    (by simpa using S.projector_mul u hu true false) (S.projector_sum u hu)]
  ext a b
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,div_pow]
  field_simp [hu,hb]
  ring

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBinaryPencil
end
