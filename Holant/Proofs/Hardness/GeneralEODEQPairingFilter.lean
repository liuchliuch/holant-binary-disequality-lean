import Holant.Proofs.Hardness.ExactTwoSignatures
import Holant.Proofs.Hardness.GeneralEOPairedCSPCycles
import Holant.OpenNetworkComposition.ProjectiveSubstitution

/-! The literal DEQ4 pairing filter of MWX Lemma64. One original row and
one DEQ4 per original ordered pair produce the full-arity restriction. Its
support cover is a proved output property, never assumed of the original row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQPairingFilter
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
namespace L
export Holant.LocalDrafts.Tractability.EOEvaluation.PairLift (Compatible restrict)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ} (p : OrientedPerfectPairing n)

def arity : Fin (p.count+1) → ℕ := Fin.cases n (fun _ => 4)

def portMap : (Σ v : Fin (p.count+1), Fin (arity p v)) → Fin n ⊕ (Fin n × Bool) :=
  fun z => Fin.cases (fun i => Sum.inr (i,false))
    (fun j => fun i : Fin 4 =>
      ![Sum.inr (p.ports (j,false),true),Sum.inr (p.ports (j,true),true),
        Sum.inl (p.ports (j,true)),Sum.inl (p.ports (j,false))] i) z.1 z.2

def portInv : Fin n ⊕ (Fin n × Bool) → (Σ v : Fin (p.count+1), Fin (arity p v))
  | .inl i => ⟨(p.ports.symm i).1.succ,if (p.ports.symm i).2 then (2 : Fin 4) else (3 : Fin 4)⟩
  | .inr (i,false) => ⟨0,i⟩
  | .inr (i,true) => ⟨(p.ports.symm i).1.succ,if (p.ports.symm i).2 then (1 : Fin 4) else (0 : Fin 4)⟩

abbrev shape : NetworkShape n where
  vertices := p.count+1
  arity := arity p
  edges := n
  ports := {
    toFun := portMap p
    invFun := portInv p
    left_inv := by
      rintro ⟨v,i⟩
      induction v using Fin.cases with
      | zero => rfl
      | succ j =>
        change Fin 4 at i
        fin_cases i <;> simp [portMap,portInv]
    right_inv := by
      intro z
      cases z with
      | inl i =>
        obtain ⟨⟨j,b⟩,rfl⟩ := p.ports.surjective i
        cases b <;> simp [portMap,portInv]
      | inr z =>
        obtain ⟨i,b⟩ := z
        cases b
        · rfl
        · obtain ⟨⟨j,b⟩,rfl⟩ := p.ports.surjective i
          cases b <;> simp [portMap,portInv] }

variable {K : Type*} [Field K]

def labels (f : Signature K n) : (v : Fin (p.count+1)) → Signature K (arity p v) :=
  Fin.cases f (fun _ => ExactTwoSignatures.E)

def network (f : Signature K n) : Network K n where
  shape := shape p
  vertex := labels p f
  edge := fun _ => Signature.disequality

def choices : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun x i := !(x i)
  invFun x i := !(x i)
  left_inv := by intro x; funext i; exact Bool.not_not _
  right_inv := by intro x; funext i; exact Bool.not_not _

theorem original_assignment (x y : Fin n → Bool) :
    (shape p).assignment x (Network.endpointChoiceAssignment (choices y))
      (0 : Fin (p.count+1)) = y := by
  funext i
  simp [shape,NetworkShape.assignment,Network.endpointChoiceAssignment,portMap,choices]

theorem filter_assignment (x y : Fin n → Bool) (j : Fin p.count) :
    (shape p).assignment x (Network.endpointChoiceAssignment (choices y)) j.succ =
      ![!(y (p.ports (j,false))),!(y (p.ports (j,true))),
        x (p.ports (j,true)),x (p.ports (j,false))] := by
  funext i
  change Fin 4 at i
  fin_cases i <;> rfl

theorem local_value (a b c d : Bool) :
    ExactTwoSignatures.E (K:=K) ![!a,!b,d,c] =
      if a=c ∧ b=d ∧ c≠d then 1 else 0 := by
  rw [ExactTwoSignatures.E_reference]
  cases a <;> cases b <;> cases c <;> cases d <;> simp

theorem all_pairs (x y : Fin n → Bool) :
    (∀ j, y (p.ports (j,false)) = x (p.ports (j,false)) ∧
      y (p.ports (j,true)) = x (p.ports (j,true)) ∧
      x (p.ports (j,false)) ≠ x (p.ports (j,true))) ↔ y=x ∧ L.Compatible p x := by
  constructor
  · intro h
    refine ⟨?_,fun j => (h j).2.2⟩
    funext i
    obtain ⟨⟨j,b⟩,rfl⟩ := p.ports.surjective i
    cases b
    · exact (h j).1
    · exact (h j).2.1
  · rintro ⟨rfl,h⟩ j
    exact ⟨rfl,rfl,h j⟩

theorem filter_product (x y : Fin n → Bool) :
    (∏ j : Fin p.count, ExactTwoSignatures.E (K:=K)
      ![!(y (p.ports (j,false))),!(y (p.ports (j,true))),
        x (p.ports (j,true)),x (p.ports (j,false))]) =
      if y=x ∧ L.Compatible p x then 1 else 0 := by
  classical
  simp only [local_value]
  by_cases h : y=x ∧ L.Compatible p x
  · rw [ite_eq_left h]
    exact Finset.prod_eq_one (fun j _ => ite_eq_left ((all_pairs p x y).mpr h j))
  · rw [ite_eq_right h]
    have bad : ¬∀ j, y (p.ports (j,false)) = x (p.ports (j,false)) ∧
        y (p.ports (j,true)) = x (p.ports (j,true)) ∧
        x (p.ports (j,false)) ≠ x (p.ports (j,true)) :=
      fun all => h ((all_pairs p x y).mp all)
    obtain ⟨j,hj⟩ := not_forall.mp bad
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

theorem denote (f : Signature K n) : (network p f).denote =
    fun x => if L.Compatible p x then f x else 0 := by
  classical
  rw [network,Network.denote_disequality]
  funext x
  change (∑ y : Fin n → Bool, ∏ v : Fin (p.count+1),
    labels p f v ((shape p).assignment x (Network.endpointChoiceAssignment y) v)) = _
  rw [← choices.sum_comp]
  have product (y : Fin n → Bool) :
      (∏ v : Fin (p.count+1), labels p f v
        ((shape p).assignment x (Network.endpointChoiceAssignment (choices y)) v)) =
      f y * (if y=x ∧ L.Compatible p x then 1 else 0) := by
    rw [Fin.prod_univ_succ]
    change f ((shape p).assignment x (Network.endpointChoiceAssignment (choices y))
      (0 : Fin (p.count+1))) *
      (∏ j : Fin p.count, ExactTwoSignatures.E
        ((shape p).assignment x (Network.endpointChoiceAssignment (choices y)) j.succ)) = _
    rw [original_assignment p x y]
    simp_rw [filter_assignment p x y]
    rw [filter_product]
  simp_rw [product]
  by_cases h : L.Compatible p x <;> simp [h]

theorem counts (f : Signature K n) :
    (network p f).shape.vertices = p.count+1 ∧ (network p f).shape.edges = n := ⟨rfl,rfl⟩

theorem native (f : Signature K n) : ∀ e,(network p f).edge e = Signature.disequality :=
  fun _ => rfl

theorem realizes (f : Signature K n) (F : SignatureFamily K)
    (hf : (⟨n,f⟩ : AnySignature K) ∈ F)
    (hE : (⟨4,ExactTwoSignatures.E⟩ : AnySignature K) ∈ F) :
    Gadget.Realizes F .disequality (fun x => if L.Compatible p x then f x else 0) := by
  rw [← denote]
  apply Gadget.realizes_network
  · intro v
    induction v using Fin.cases with
    | zero => exact hf
    | succ j => exact hE
  · exact native p f

theorem restricted_cover (f : Signature AlgebraicComplex n) :
    GeneralEOPairedCSPCycles.Covers p (L.restrict p f) := by
  intro x hx
  by_contra hn
  exact hx (ite_eq_right hn)

/-- The compressed table is literally the original chosen pairing table. -/
theorem compressed_restriction (f : Signature AlgebraicComplex n) :
    p.restrict (L.restrict p f) = p.restrict f := by
  funext x
  apply ite_eq_left
  intro j
  simp [OrientedPerfectPairing.word]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQPairingFilter
