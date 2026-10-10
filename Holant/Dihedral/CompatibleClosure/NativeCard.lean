import Holant.NetworkGluing.Finite
import Holant.NetworkAsGadget
import Holant.Marked.Basic

/-! A literal two-vertex, two-native-X-edge contraction. The original tensor
and actual binary representative are the only vertex resources. -/
noncomputable section
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked Holant.Tractable
set_option backward.isDefEq.respectTransparency false

private abbrev arity (n : ℕ) : Bool → ℕ | false => n+2 | true => 2

private def ports (n : ℕ) : (Σ v : Bool, Fin (arity n v)) ≃ (Fin n ⊕ (Bool × Bool)) where
  toFun
    | ⟨false,i⟩ => Fin.cases (.inr (false,false))
        (Fin.cases (.inr (true,false)) Sum.inl) i
    | ⟨true,i⟩ => Fin.cases (.inr (false,true)) (fun _ => .inr (true,true)) i
  invFun
    | .inl i => ⟨false,i.succ.succ⟩
    | .inr (e,false) => ⟨false,if e then 1 else 0⟩
    | .inr (e,true) => ⟨true,if e then 1 else 0⟩
  left_inv := by
    rintro ⟨v,i⟩
    cases v
    · refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl
    · fin_cases i <;> rfl
  right_inv := by
    rintro (i | ⟨e,b⟩)
    · rfl
    · cases e <;> cases b <;> rfl

/-- Both native edge orientations go from the original q vertex to the
actual binary representative; all surviving q ports keep their order. -/
def nativeCardFinite {n : ℕ} (q : Signature Scalar (n+2)) (C : Mat) :
    FiniteNetwork Scalar Bool Bool n where
  arity := arity n
  ports := ports n
  vertex
    | false => q
    | true => kernelSignature C
  edge := fun _ => Signature.disequality

def nativeCard {n : ℕ} (q : Signature Scalar (n+2)) (C : Mat) : Network Scalar n :=
  (nativeCardFinite q C).toNetwork

private def assignments : ((Bool × Bool) → Bool) ≃ (Bool × Bool × Bool × Bool) where
  toFun z := (z (false,false),z (false,true),z (true,false),z (true,true))
  invFun q p := if p.1 then (if p.2 then q.2.2.2 else q.2.2.1)
    else (if p.2 then q.2.1 else q.1)
  left_inv := by intro z; funext p; rcases p with ⟨e,b⟩; cases e <;> cases b <;> rfl
  right_inv := by intro q; rfl

def nativeCardValue {n : ℕ} (q : Signature Scalar (n+2)) (C : Mat) : Signature Scalar n :=
  fun x => ∑ a : Bool, ∑ b : Bool, C (!a) (!b) * q (Fin.cons a (Fin.cons b x))

/-- Exact finite-sum bridge, including the two native-X complements. -/
theorem nativeCard_denote {n : ℕ} (q : Signature Scalar (n+2)) (C : Mat) :
    (nativeCard q C).denote = nativeCardValue q C := by
  rw [nativeCard,FiniteNetwork.denote_toNetwork]
  funext x
  letI : DecidableEq (Bool × Bool) := @instDecidableEqProd Bool Bool (Classical.decEq Bool) instDecidableEqBool
  unfold FiniteNetwork.denote
  have hq (z : (Bool × Bool) → Bool) :
      (fun i : Fin (n+2) => Sum.elim x z ((ports n) ⟨false,i⟩)) =
        Fin.cons (z (false,false)) (Fin.cons (z (true,false)) x) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl
  have hc (z : (Bool × Bool) → Bool) :
      (fun i : Fin 2 => Sum.elim x z ((ports n) ⟨true,i⟩)) =
        ![z (false,true),z (true,true)] := by
    funext i
    fin_cases i <;> rfl
  change (∑ z : (Bool × Bool) → Bool,
    (∏ v : Bool, (nativeCardFinite q C).vertex v (fun i => Sum.elim x z ((ports n) ⟨v,i⟩))) *
      ∏ e : Bool, Signature.disequality (z (e,false)) (z (e,true))) = _
  simp only [Fintype.prod_bool]
  change (∑ z : (Bool × Bool) → Bool,
    C (z (false,true)) (z (true,true)) *
      q (fun i => Sum.elim x z ((ports n) ⟨false,i⟩)) *
      (Signature.disequality (z (true,false)) (z (true,true)) *
        Signature.disequality (z (false,false)) (z (false,true)))) = _
  simp only [hq]
  rw [← assignments.symm.sum_comp]
  simp [Fintype.sum_prod_type,nativeCardValue,Fintype.sum_bool,assignments,
    Equiv.coe_fn_symm_mk,Signature.disequality]

/-- Provenance is exact: q and C are supplied actual signatures; no analytic
monomial factor or arbitrary basis matrix is introduced as a vertex. -/
theorem nativeCard_realizes {n : ℕ} (F : SignatureFamily Scalar)
    (q : Signature Scalar (n+2)) (C : Mat)
    (hq : (⟨n+2,q⟩ : AnySignature Scalar) ∈ F)
    (hc : (⟨2,kernelSignature C⟩ : AnySignature Scalar) ∈ F) :
    Gadget.Realizes F .disequality (nativeCardValue q C) := by
  have hh := Gadget.realizes_network (nativeCard q C) F .disequality
    (by
      intro v
      change (⟨arity n ((Fintype.equivFin Bool).symm v),
        (nativeCardFinite q C).vertex ((Fintype.equivFin Bool).symm v)⟩ : AnySignature Scalar) ∈ F
      cases h : (Fintype.equivFin Bool).symm v
      · exact hq
      · exact hc)
    (by intro e; rfl)
  rwa [nativeCard_denote] at hh

@[simp] theorem nativeCard_vertices {n : ℕ} (q : Signature Scalar (n+2)) (C : Mat) :
    (nativeCard q C).shape.vertices = 2 := rfl
@[simp] theorem nativeCard_edges {n : ℕ} (q : Signature Scalar (n+2)) (C : Mat) :
    (nativeCard q C).shape.edges = 2 := rfl

end Holant.Dihedral.CompatibleClosure
