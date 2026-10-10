import Holant.Certificates.EqualityQuaternary.MonomialDeck
import Holant.ReedMuller.TwoChart.NativeXExpansion
import Holant.EightVertex.ProductAnchor.GeneralizedEquality

/-! An exact native-X gadget for any selected original-coordinate bit flips.
Its only nonbinary vertex is one occurrence of the original q. Binary X labels
are expanded into literal equality vertices, rather than assumed free resources.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary
open Holant Holant.Marked Holant.Tractable Holant.Marked.SupportAtlas
namespace Flip
open Holant.ReedMuller.TwoChart.NativeXExpansion
set_option backward.isDefEq.respectTransparency false

def value (q : Signature Scalar 4) (mask : Word) : Signature Scalar 4 :=
  fun x => q (xorWord x mask)

def arity : Fin 5 → ℕ := Fin.cases 4 (fun _ => 2)
def portMap : (Σ v : Fin 5, Fin (arity v)) → (Fin 4 ⊕ (Fin 4 × Bool)) :=
  fun p => Fin.cases (fun i => .inr (i,false))
    (fun j => fun i : Fin 2 => if i = 0 then .inl j else .inr (j,true)) p.1 p.2
def portInv : (Fin 4 ⊕ (Fin 4 × Bool)) → (Σ v : Fin 5, Fin (arity v))
  | .inl j => ⟨j.succ,(0 : Fin 2)⟩
  | .inr (j,false) => ⟨0,j⟩
  | .inr (j,true) => ⟨j.succ,(1 : Fin 2)⟩
def shape : NetworkShape 4 where
  vertices := 5
  arity := arity
  edges := 4
  ports := {
    toFun := portMap
    invFun := portInv
    left_inv p := by
      rcases p with ⟨v,i⟩
      fin_cases v <;> dsimp [arity] at i <;> fin_cases i <;> rfl
    right_inv p := by
      cases p with
      | inl j => fin_cases j <;> rfl
      | inr p => rcases p with ⟨j,b⟩; fin_cases j <;> cases b <;> rfl }

def leg (b : Bool) : Mat := if b then Signature.equality else Signature.disequality
def labels (q : Signature Scalar 4) (mask : Word) : (v : Fin 5) → Signature Scalar (arity v) :=
  Fin.cases q (fun j => kernelSignature (leg (mask j)))
def rawNetwork (q : Signature Scalar 4) (mask : Word) : Network Scalar 4 where
  shape := shape
  vertex := labels q mask
  edge := fun _ => Signature.disequality

theorem leg_entry (m a b : Bool) : leg m a (!b) = Signature.equality (a ^^ m) b := by
  cases m <;> cases a <;> cases b <;> rfl

def choices : Word ≃ Word where
  toFun := complement
  invFun := complement
  left_inv := complement_complement
  right_inv := complement_complement

theorem raw_product (q : Signature Scalar 4) (mask x y : Word) :
    (∏ v : Fin 5, labels q mask v
      (shape.assignment x (Network.endpointChoiceAssignment (choices y)) v)) =
      q y * ∏ j : Fin 4, Signature.equality (xorWord x mask j) (y j) := by
  have hq : shape.assignment x (Network.endpointChoiceAssignment (choices y)) (0 : Fin 5) = y := by
    funext i
    fin_cases i <;> simp [shape,NetworkShape.assignment,Network.endpointChoiceAssignment,
      portMap,choices,complement]
  simp only [Fin.prod_univ_succ]
  change q (shape.assignment x (Network.endpointChoiceAssignment (choices y)) (0 : Fin 5)) * _ = _
  rw [hq]
  change q y * (leg (mask 0) (x 0) (!(y 0)) *
    (leg (mask 1) (x 1) (!(y 1)) * (leg (mask 2) (x 2) (!(y 2)) *
      (leg (mask 3) (x 3) (!(y 3)) * 1)))) = _
  simp [leg_entry,xorWord]

theorem raw_denote (q : Signature Scalar 4) (mask : Word) :
    (rawNetwork q mask).denote = value q mask := by
  rw [rawNetwork,Network.denote_disequality]
  funext x
  change (∑ c : Word, ∏ v : Fin 5,labels q mask v
    (shape.assignment x (Network.endpointChoiceAssignment c) v)) = _
  rw [←choices.sum_comp]
  simp_rw [raw_product,Signature.prod_equality]
  simp [value]

/-- X labels are replaced by I-X-I paths. All actual edges are native X. -/
def network (q : Signature Scalar 4) (mask : Word) : Network Scalar 4 := expand (rawNetwork q mask)

theorem denote (q : Signature Scalar 4) (mask : Word) :
    (network q mask).denote = value q mask := by
  rw [network,denote_expand,raw_denote]

theorem native (q : Signature Scalar 4) (mask : Word) :
    ∀ e, (network q mask).edge e = Signature.disequality :=
  native_edges _ (fun _ => rfl)

theorem zero_kept (q : Signature Scalar 4) (mask : Word) :
    ¬IsX (rawNetwork q mask) (0 : Fin 5) := by
  intro h
  have := congrArg Sigma.fst h
  change 4 = 2 at this
  omega

def ancestor (q : Signature Scalar 4) (mask : Word) : Fin (network q mask).shape.vertices :=
  vertexEquiv _ (.inl ⟨(0 : Fin 5),zero_kept q mask⟩)

/-- Exact resource-count witness: one original q occurrence, all others literal I. -/
theorem labels_exact (q : Signature Scalar 4) (mask : Word) :
    (⟨(network q mask).shape.arity (ancestor q mask),
      (network q mask).vertex (ancestor q mask)⟩ : AnySignature Scalar) = ⟨4,q⟩ ∧
    ∀ v, v ≠ ancestor q mask →
      (⟨(network q mask).shape.arity v,(network q mask).vertex v⟩ : AnySignature Scalar) =
        ⟨2,kernelSignature Signature.equality⟩ := by
  refine ⟨?_,?_⟩
  · exact kept_label (rawNetwork q mask) ⟨(0 : Fin 5),zero_kept q mask⟩
  intro v hv
  obtain ⟨w,rfl⟩ := (vertexEquiv (rawNetwork q mask)).surjective v
  cases w with
  | inr w => exact replacement_label _ w.1 w.2
  | inl w =>
    change (⟨(expand (rawNetwork q mask)).shape.arity _,
      (expand (rawNetwork q mask)).vertex _⟩ : AnySignature Scalar) = _
    rw [kept_label]
    have hw : w.val ≠ (0 : Fin 5) := by
      intro he
      apply hv
      apply congrArg (vertexEquiv (rawNetwork q mask))
      congr 1
      exact Subtype.ext he
    rcases w with ⟨v,hkept⟩
    induction v using Fin.cases with
    | zero => exact False.elim (hw rfl)
    | succ j =>
      cases hm : mask j
      · exact False.elim (hkept (by
          simp [rawNetwork,labels,shape,arity,leg,hm]
          rfl))
      · simp [rawNetwork,labels,shape,arity,leg,hm]

theorem realizes (q : Signature Scalar 4) (mask : Word) :
    Gadget.Realizes ({p | p = ⟨4,q⟩ ∨ p = ⟨2,kernelSignature Signature.equality⟩})
      .disequality (value q mask) := by
  rw [←denote]
  apply Gadget.realizes_network
  · intro v
    by_cases hv : v = ancestor q mask
    · exact Or.inl (hv ▸ (labels_exact q mask).1)
    · exact Or.inr ((labels_exact q mask).2 v hv)
  · exact native q mask

theorem actual (F : SignatureFamily Scalar) (q : Signature Scalar 4)
    (hq : Gadget.Realizes F .disequality q)
    (hI : Gadget.Realizes F .disequality (kernelSignature Signature.equality)) (mask : Word) :
    Gadget.Realizes F .disequality (value q mask) := by
  have h := realizes_dressMask F q Signature.equality hq hI mask
  have he : dressMask q Signature.equality mask = value q mask := by
    funext x
    have h := sector_dressMask InvertibleKernel.identity q Signature.equality 1
      (by
        funext a b
        cases a <;> cases b <;>
          simp [sectorTransfer,conjugate,InvertibleKernel.identity,InvertibleKernel.symm,
            Kernel.mul_apply,Signature.equality,Signature.disequality,scale]) mask x
    simpa [dressingMultiplier,value] using h
  rwa [he] at h

end Flip
end Holant.Certificates.EqualityQuaternary
