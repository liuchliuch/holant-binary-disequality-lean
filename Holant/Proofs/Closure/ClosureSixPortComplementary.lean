import Holant.Proofs.Closure.ClosureSixPortFixedPorts
import Holant.Proofs.Closure.ClosureRootPencilProduct

/-! NEW UNVERIFIED literal complementary-sector support. This is the payload
that the actual root-pencil/binary classification must internally produce;
no classification function is added as a final base-case input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant Holant.Projective

structure ComplementarySector (m : ℕ) (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (p : Bool) where
  ports : (Fin 2 × Bool) ≃ Fin 4
  fixed : Mat
  rooted : IsRootMonomial m fixed
  parity : Bool
  orientation : Bool
  coefficient : Bool → ℂ
  nonzero : ∀ a, coefficient a ≠ 0
  endpoints : ∀ a x, sliceSix h e p a x =
    fixed (x (ports (0,false))) (x (ports (0,true))) *
      (coefficient a • parityAxis parity (orientation ^^ a))
        (x (ports (1,false))) (x (ports (1,true)))

def ComplementarySector.fixedParity {m : ℕ} {h : Signature ℂ 6} {e : Equiv.Perm (Fin 6)} {p : Bool}
    (D : ComplementarySector m h e p) : Bool :=
  Classical.choose (ClosureRootPencil.root_support D.rooted)

theorem ComplementarySector.fixedParity_spec {m : ℕ} {h : Signature ℂ 6}
    {e : Equiv.Perm (Fin 6)} {p : Bool} (D : ComplementarySector m h e p) (a b : Bool) :
    D.fixed a b ≠ 0 ↔ b = (a ^^ D.fixedParity) :=
  Classical.choose_spec (ClosureRootPencil.root_support D.rooted) a b

theorem scaled_axis_support (p r a b : Bool) (c : ℂ) (hc : c ≠ 0) :
    (c • parityAxis p r) a b ≠ 0 ↔ a=r ∧ b=(r^^p) := by
  simp [parityAxis,hc]

theorem ComplementarySector.endpoint_support {m : ℕ} {h : Signature ℂ 6}
    {e : Equiv.Perm (Fin 6)} {p : Bool} (D : ComplementarySector m h e p) (a : Bool) (x : Word 4) :
    sliceSix h e p a x ≠ 0 ↔
      x (D.ports (0,true)) = (x (D.ports (0,false)) ^^ D.fixedParity) ∧
      x (D.ports (1,false)) = (D.orientation ^^ a) ∧
      x (D.ports (1,true)) = ((D.orientation ^^ a) ^^ D.parity) := by
  rw [D.endpoints,mul_ne_zero_iff,D.fixedParity_spec,
    scaled_axis_support D.parity (D.orientation^^a) _ _ _ (D.nonzero a)]

/-- Exact original-word support in this sector, with literal port incidence
and every nonzero endpoint coefficient preserved. -/
theorem ComplementarySector.word_support {m : ℕ} {h : Signature ℂ 6}
    {e : Equiv.Perm (Fin 6)} {p : Bool} (D : ComplementarySector m h e p)
    (w : Word 6) (hp : (w (e 0) ^^ w (e 1))=p) :
    h w ≠ 0 ↔
      residualSix e w (D.ports (0,true)) =
        (residualSix e w (D.ports (0,false)) ^^ D.fixedParity) ∧
      residualSix e w (D.ports (1,false)) = (D.orientation ^^ w (e 0)) ∧
      residualSix e w (D.ports (1,true)) = ((D.orientation ^^ w (e 0)) ^^ D.parity) := by
  have endpoint := D.endpoint_support (w (e 0)) (residualSix e w)
  have reconstruct : fillSix e (w (e 0)) p (residualSix e w)=w := by
    rw [←hp]
    exact fillSix_reconstruct e w
  unfold sliceSix at endpoint
  rw [reconstruct] at endpoint
  exact endpoint

/-- Exact fixed binary from this C payload exposes the Z/C factor. -/
def ComplementarySector.zero_split {m : ℕ} {h : Signature ℂ 6}
    {e : Equiv.Perm (Fin 6)} {p : Bool} (D : ComplementarySector m h e p)
    (zero : ZeroSector h e (!p)) :
    Holant.LocalDrafts.FinitePGL2.Stabilization.ProperSplit (⟨6,h⟩ : AnySignature ℂ)
      ⟨2,binaryWord D.fixed⟩
      ⟨4,(commonResidualOfPorts h e p D.ports D.fixed
        (fun a => D.coefficient a • parityAxis D.parity (D.orientation^^a)) D.endpoints).remainder⟩ :=
  zero_fixed_ports_split h e p zero D.ports D.fixed
    (fun a => D.coefficient a • parityAxis D.parity (D.orientation^^a)) D.endpoints

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
