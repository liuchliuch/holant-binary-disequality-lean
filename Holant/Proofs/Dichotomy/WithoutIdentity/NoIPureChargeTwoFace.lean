import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureOddFace
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureChargeTwoWords

/-! Under uniform parity, two support classes separated by charge two
produce an actual two-corner face with that exact residue. Minimality is
internal, and every agreed coordinate is removed by a literal native pin. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoFace
open Holant
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false

def color {n : ℕ} (x : Fin n→Bool) : Bool:=decide (2≤weight x%4)

theorem colors_differ {n : ℕ} (x y : Fin n→Bool)
    (charge : ((weight x : ℤ)-weight y)%4=2) : color x≠color y := by
  intro same
  have h : (2≤weight x%4)↔(2≤weight y%4):=decide_eq_decide.mp same
  omega

theorem charge_of_colors {n : ℕ} (x y : Fin n→Bool)
    (parity : NoIPureOddFace.color x=NoIPureOddFace.color y)
    (different : color x≠color y) : ((weight x : ℤ)-weight y)%4=2 := by
  have hp : (weight x%2=1)↔(weight y%2=1):=decide_eq_decide.mp parity
  have hd : ¬((2≤weight x%4)↔(2≤weight y%4)):=fun h=>different (decide_eq_decide.mpr h)
  omega

variable {K : Type} [Field K] [Algebra ℚ K] {s : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (arity i.val))
variable (pins : Bool→NativeAntiTargetSource.Output H 1)
variable (pinsForm : ∀bit,(pins bit).network.denote=NoIPurePinProjection.pin bit)

include pinsForm in
theorem source {n : ℕ} (N : NativeAntiTargetSource.Output H n)
    (parity : NoIPureOddFace.UniformParity N.network.denote)
    (mixed : ∃x y,N.network.denote x≠0 ∧ N.network.denote y≠0 ∧ ((weight x : ℤ)-weight y)%4=2) :
    ∃m,0<m ∧ ∃R : NativeAntiTargetSource.Output H m,∃mask : Fin m→Bool,∃u v : K,
      u≠0 ∧ v≠0 ∧ Holant.charge mask%4=2 ∧ R.network.denote=NoIPureChargeTwoWords.row mask u v := by
  have available : ∃x y,N.network.denote x≠0 ∧ N.network.denote y≠0 ∧ color x≠color y := by
    obtain ⟨x,y,hx,hy,charge⟩:=mixed
    exact ⟨x,y,hx,hy,colors_differ x y charge⟩
  obtain ⟨x,y,hx,hy,hc,face⟩:=NoIPureTwoColorFace.source N.network.denote color available
  have different : x≠y:=fun same=>hc (congrArg color same)
  obtain ⟨m,positive,_distance,R,mask,charge_eq,form⟩:=NoIPurePinFace.source H pins pinsForm N x y different face
  obtain ⟨b,uniform⟩:=parity
  refine ⟨m,positive,R,mask,N.network.denote x,N.network.denote y,hx,hy,?_,form⟩
  rw [charge_eq]
  exact charge_of_colors x y ((uniform x hx).trans (uniform y hy).symm) hc

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoFace
end
