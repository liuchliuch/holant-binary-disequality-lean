import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeFiniteCaps
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeDenseOrders

/-! The complete order-two odd-cap test forces one complementary sign even
when middle coefficients vanish. Four literal pencils suffice; all zero
cases are handled algebraically without any density assumption. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseOrderTwo
open Holant Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.Projective.CyclicPhasePencil
namespace P
export PaperTerminalBridgeFiniteCaps (Samples sample_power)
end P
namespace O
export PaperTerminalBridgeDenseOrders (order reordered entries_reordered)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

theorem pencil (a b c d : K)
    (samples : ∀t : K,t^2=1→ScalarSample 2 (a+t*c) (b+t*d)) :
    a*c=b*d ∧ a^2+c^2=b^2+d^2 := by
  have pos := P.sample_power (K:=K) (m:=2) (by omega) _ _ (samples 1 (by norm_num))
  have neg := P.sample_power (K:=K) (m:=2) (by omega) _ _ (samples (-1) (by norm_num))
  constructor
  · linear_combination (neg-pos)/4
  · linear_combination -(neg+pos)/2

theorem coefficients (e : Entries K) (samples : P.Samples 2 e)
    (extra : ∀t : K,t^2=1→ScalarSample 2 (e.y+t*e.c) (e.z+t*e.b)) :
    ∃ε : K,ε^2=1 ∧ e.b=ε*e.y ∧ e.c=ε*e.z ∧ e.d=ε*e.w := by
  have first := pencil e.w e.z e.c e.d samples.first
  have second := pencil e.w e.y e.b e.d samples.second
  have opposite := pencil e.c e.w e.d e.z samples.opposite
  have third := (pencil e.y e.z e.c e.b extra).1
  have csquare : e.c^2=e.z^2 := by linear_combination (first.2+opposite.2)/2
  have wsquare : e.w^2=e.d^2 := by linear_combination (first.2-opposite.2)/2
  have bsquare : e.b^2=e.y^2 := by linear_combination second.2-wsquare
  by_cases hz : e.z≠0
  · refine ⟨e.c/e.z,?_,?_,?_,?_⟩
    · rw [div_pow,csquare,div_self (pow_ne_zero _ hz)]
    · apply (mul_left_cancel₀ hz)
      field_simp
      linear_combination -third
    · field_simp
    · apply (mul_left_cancel₀ hz)
      field_simp
      linear_combination -first.1
  have zzero : e.z=0 := not_ne_iff.mp hz
  have czero : e.c=0 := by
    by_contra live
    exact pow_ne_zero 2 live (by rw [csquare,zzero];norm_num)
  by_cases hw : e.w≠0
  · refine ⟨e.d/e.w,?_,?_,?_,?_⟩
    · rw [div_pow,←wsquare,div_self (pow_ne_zero _ hw)]
    · apply (mul_left_cancel₀ hw)
      field_simp
      linear_combination second.1
    · simp [czero,zzero]
    · field_simp
  have wzero : e.w=0 := not_ne_iff.mp hw
  have dzero : e.d=0 := by
    by_contra live
    exact pow_ne_zero 2 live (by rw [←wsquare,wzero];norm_num)
  by_cases hy : e.y≠0
  · refine ⟨e.b/e.y,?_,?_,?_,?_⟩
    · rw [div_pow,bsquare,div_self (pow_ne_zero _ hy)]
    · field_simp
    · simp [czero,zzero]
    · simp [dzero,wzero]
  have yzero : e.y=0 := not_ne_iff.mp hy
  have bzero : e.b=0 := by
    by_contra live
    exact pow_ne_zero 2 live (by rw [bsquare,yzero];norm_num)
  exact ⟨1,by simp,by simp [bzero,yzero],by simp [czero,zzero],by simp [dzero,wzero]⟩

theorem source (f : Signature K 4)
    (samples : ∀e : Equiv.Perm (Fin 4),P.Samples 2 (entries (Tensor.reindex e f))) :
    ∃ε : K,ε^2=1 ∧ (entries f).b=ε*(entries f).y ∧
      (entries f).c=ε*(entries f).z ∧ (entries f).d=ε*(entries f).w := by
  have base : P.Samples 2 (entries f) := by simpa [Tensor.reindex] using samples (Equiv.refl _)
  have changed := samples (O.order 2)
  change P.Samples 2 (entries (O.reordered f 2)) at changed
  rw [O.entries_reordered] at changed
  exact coefficients (entries f) base changed.first


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseOrderTwo
end
