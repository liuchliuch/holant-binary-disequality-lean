import Holant.Proofs.Hardness.GeneralOddHighTerminalCharge
import Holant.Proofs.Hardness.GeneralOddUnarySource
import Holant.Proofs.Tetrahedral.ExternalOddCompletion.Structure

/-! The coprime-charge unary producer applied to the actual high-odd Eq-loop
terminal.  Every output vertex is an original ordinary row, every physical
edge is Eq, and the original two label arities give an exact edge budget.
The coprimality premise is explicit and is not inferred from failure of Tract. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddHighTerminalSource
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.GeneralExtraction
open NamedContraction SupportDescent SupportCaps NativeCopies
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open GeneralOddUnaryOrdinary GeneralOddUnarySource
namespace Structure
export Holant.LocalDrafts.TetrahedralCompletion.ExternalOddCompletion.Structure
  (twoConstants ordinary_terminal_decomposition)
end Structure
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (j : Fin s) (ho : Odd (a j.val)) (hnz : G j≠0)

abbrev high := (result G j ho hnz).frame.network G
abbrev diagnostic := sourceKBasis.symm.action (high G j ho hnz).denote
abbrev endpoint (b : Bool) := diagnostic G j ho hnz (fun _ => b)

private theorem cast_signature_eq {m n : ℕ} (h : m=n)
    (f : Signature AlgebraicComplex n) :
    (⟨n,f⟩ : AnySignature AlgebraicComplex)=
      ⟨m,fun x => f (fun i => x (Fin.cast h.symm i))⟩ := by
  cases h
  rfl

theorem high_uses : Uses (high G j ho hnz) (original G) := by
  intro v
  refine ⟨j,?_⟩
  let D := (result G j ho hnz).frame
  change (⟨a j.val,G j⟩ : AnySignature AlgebraicComplex)=
    ⟨D.shape.arity v,fun x => G j (fun i => x (Fin.cast (D.labels.vertex_arity v) i))⟩
  exact cast_signature_eq (D.originalArity v) (G j)

theorem high_ordinary : Ordinary (high G j ho hnz) := fun _ => rfl

/-- A supported endpoint is produced by the actual high-odd no-cut theorem.
Its value is kept exactly; no nonzero endpoint is chosen by normalization. -/
theorem supported_endpoint (hh : 3≤(result G j ho hnz).arity) :
    ∃ b : Bool,endpoint G j ho hnz (!b)≠0 := by
  have hd := Structure.ordinary_terminal_decomposition (high G j ho hnz).denote
    (result G j ho hnz).odd hh (result G j ho hnz).stopped
  by_contra h
  push_neg at h
  have h0 := h true
  have h1 := h false
  simp only [Bool.not_true,Bool.not_false] at h0 h1
  have hz : diagnostic G j ho hnz=0 := by
    rw [show diagnostic G j ho hnz=Structure.twoConstants
      (endpoint G j ho hnz false) (endpoint G j ho hnz true) from hd,h0,h1]
    funext x
    simp [Structure.twoConstants,purePin]
  apply (result G j ho hnz).nonzero
  have he := congrArg sourceKBasis.action hz
  rw [diagnostic,InvertibleKernel.action_symm_action] at he
  exact he.trans (Signature.coordinateAction_zero _)

/-- Original input entry: one selected original odd label and one actual
supported original row of opposite coprime charge yield a genuine unary.
No hard basis, free factor, pin or output unary is supplied as input. -/
theorem source (hh : 3≤(result G j ho hnz).arity) (b : Bool)
    (hy : endpoint G j ho hnz (!b)≠0) (k : Fin s)
    (x : Fin (a k.val) → Bool) (hx : sourceKBasis.symm.action (G k) x≠0)
    (q : ℕ) (hq : 0<q) (hcharge : balance b x=q)
    (hcop : Nat.Coprime q (result G j ho hnz).arity) :
    ∃ r t : ℕ, 0<r ∧ r<(result G j ho hnz).arity ∧ t<q ∧
      r*q=t*(result G j ho hnz).arity+1 ∧
      ∃ U : Network AlgebraicComplex 1, Uses U (original G) ∧ Ordinary U ∧
        sourceKBasis.symm.action U.denote (fun _ => b)≠0 ∧ U.denote≠0 ∧
        U.shape.vertices=r+t ∧
        1+2*U.shape.edges=r*a k.val+t*a j.val ∧
        U.shape.vertices≤a j.val+a k.val-2 := by
  let P := toNative (Network.corolla (G k))
  let H := toNative (high G j ho hnz)
  have hPF : Uses P (kCoordinates (original G)) :=
    toNative_uses (original G) _ (fun _ => ⟨k,rfl⟩)
  have hPX : Native P := toNative_native _ (fun e => Fin.elim0 e)
  have hHF : Uses H (kCoordinates (original G)) :=
    toNative_uses (original G) _ (high_uses G j ho hnz)
  have hHX : Native H := toNative_native _ (high_ordinary G j ho hnz)
  have hx' : P.denote x≠0 := by
    simpa [P,toNative_denote,Network.denote_corolla] using hx
  have hy' : H.denote (fun _ => !b)≠0 := by
    simpa [H,toNative_denote] using hy
  obtain ⟨r,t,hr,hrn,htq,he,U,hUF,hUX,hUb,hUv,hUe⟩ :=
    GeneralOddHighTerminalCharge.opposite_coprime (kCoordinates (original G))
      (by norm_num) b P H hPF hPX hHF hHX x hx' hy' q hq hcharge (by omega) hcop
  have hdiag : sourceKBasis.symm.action (toOrdinary U).denote=U.denote := by
    rw [toOrdinary_denote,InvertibleKernel.symm_action_action]
  have hUnz : (toOrdinary U).denote≠0 := by
    intro hz
    have he := congrArg sourceKBasis.symm.action hz
    rw [hdiag] at he
    have hzero := he.trans (Signature.coordinateAction_zero _)
    exact hUb (congrFun hzero (fun _ => b))
  have hvertices : (toOrdinary U).shape.vertices=r+t := by
    change U.shape.vertices=r+t
    have hH : H.shape.vertices=1 := (result G j ho hnz).frame.one
    have hP : P.shape.vertices=1 := rfl
    simpa [hH,hP] using hUv
  have hecon := Loops.selected_conservation G j ho hnz
  have hedge : 1+2*(toOrdinary U).shape.edges=r*a k.val+t*a j.val := by
    change 1+2*U.shape.edges=_
    have hP : P.shape.edges=0 := rfl
    have hH : H.shape.edges=(result G j ho hnz).frame.shape.edges := rfl
    simpa only [hP,hH,Nat.mul_zero,Nat.add_zero,hecon] using hUe
  have hqbound : q≤a k.val := by
    have hc := balance_count b x
    have hl := matches_le b x
    simp only [Fintype.card_fin] at hc hl
    omega
  refine ⟨r,t,hr,hrn,htq,he,toOrdinary U,toOrdinary_uses (original G) U hUF,
    toOrdinary_ordinary U hUX,?_,hUnz,hvertices,hedge,?_⟩
  · rw [hdiag]
    exact hUb
  · rw [hvertices]
    have harity := (result G j ho hnz).arity_le
    omega

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddHighTerminalSource
