import Holant.Proofs.Algorithms.TransformRecognition.FiniteBranchEnumeration
import Holant.Tractable.Criteria


namespace Holant.LocalDrafts.Tractability.EOEvaluation.EOConditionCertificate.Pairings
open Holant.Tractable
open Holant.LocalDrafts.MainChain.TransformRecognition

abbrev Slot (n : ℕ) := Fin (n/2) × Bool
abbrev Template (n : ℕ) := Slot n ≃ Fin n

def slots (n : ℕ) : List (Slot n) :=
  (List.finRange (n/2)).flatMap (fun i => [(i,false),(i,true)])

theorem mem_slots {n : ℕ} (q : Slot n) : q ∈ slots n := by
  rcases q with ⟨i,b⟩
  apply List.mem_flatMap.mpr
  refine ⟨i,List.mem_finRange i,?_⟩
  cases b <;> simp

def mappings : (n : ℕ) → List (Slot n → Fin n)
  | 0 => [fun q => Fin.elim0 q.1]
  | n+1 => FiniteBranchEnumeration.assignments (List.finRange (n+1)) 0 (slots (n+1))

theorem mem_mappings {n : ℕ} (f : Slot n → Fin n) : f ∈ mappings n := by
  cases n with
  | zero =>
      have hf : f = fun q => Fin.elim0 q.1 := by
        funext q
        exact Fin.elim0 q.1
      simp [mappings,hf]
  | succ n =>
      obtain ⟨g,hg,he⟩ := FiniteBranchEnumeration.assignments_complete
        (List.finRange (n+1)) (0 : Fin (n+1)) (slots (n+1)) f
        (fun _ _ => List.mem_finRange _)
      have hgf : g=f := funext (fun q => he q (mem_slots q))
      simpa only [mappings,hgf] using hg

def accepted (n : ℕ) : List (Slot n → Fin n) :=
  (mappings n).filter (fun f => decide (Function.Bijective f))

theorem inverse_found {n : ℕ} (f : Slot n → Fin n) (hf : Function.Bijective f) (j : Fin n) :
    ((slots n).find? (fun q => decide (f q=j))).isSome := by
  obtain ⟨q,hq⟩ := hf.2 j
  exact List.find?_isSome.mpr ⟨q,mem_slots q,decide_eq_true hq⟩

def inverse {n : ℕ} (f : Slot n → Fin n) (hf : Function.Bijective f) (j : Fin n) : Slot n :=
  ((slots n).find? (fun q => decide (f q=j))).get (inverse_found f hf j)

theorem inverse_right {n : ℕ} (f : Slot n → Fin n) (hf : Function.Bijective f) (j : Fin n) :
    f (inverse f hf j)=j := by
  have h : (slots n).find? (fun q => decide (f q=j))=some (inverse f hf j) :=
    Option.eq_some_of_isSome (inverse_found f hf j)
  have hp : (fun q : Slot n => decide (f q=j)) (inverse f hf j)=true := List.find?_some (p:=fun q : Slot n => decide (f q=j)) h
  exact of_decide_eq_true hp

def equiv {n : ℕ} (f : Slot n → Fin n) (hf : Function.Bijective f) : Template n where
  toFun := f
  invFun := inverse f hf
  left_inv q := hf.1 (inverse_right f hf (f q))
  right_inv := inverse_right f hf

def templates (n : ℕ) : List (Template n) :=
  (accepted n).attach.map (fun f => equiv f.val (by
    have hp : decide (Function.Bijective f.val)=true :=
      (List.mem_filter.mp (show f.val ∈ (mappings n).filter
        (fun g => decide (Function.Bijective g)) from f.property)).2
    exact of_decide_eq_true hp))

theorem mem_templates {n : ℕ} (p : Template n) : p ∈ templates n := by
  have hp : p.toFun ∈ accepted n :=
    List.mem_filter.mpr ⟨mem_mappings p.toFun,decide_eq_true p.bijective⟩
  unfold templates
  apply List.mem_map.mpr
  refine ⟨⟨p.toFun,hp⟩,List.mem_attach _ _,?_⟩
  exact Equiv.ext (fun _ => rfl)

theorem twice_count {n : ℕ} (p : OrientedPerfectPairing n) : 2*p.count=n := by
  simpa [Fintype.card_prod,Nat.mul_comm] using Fintype.card_congr p.ports

theorem count_eq_half {n : ℕ} (p : OrientedPerfectPairing n) : p.count=n/2 := by
  have h := twice_count p
  omega

def normalize {n : ℕ} (p : OrientedPerfectPairing n) : Template n :=
  (Equiv.prodCongr (finCongr (count_eq_half p)).symm (Equiv.refl Bool)).trans p.ports

def pairing {n : ℕ} (p : Template n) : OrientedPerfectPairing n := ⟨n/2,p⟩

theorem normalize_exact {n : ℕ} (p : OrientedPerfectPairing n) : pairing (normalize p)=p := by
  rcases p with ⟨d,e⟩
  have hd : d=n/2 := count_eq_half (⟨d,e⟩ : OrientedPerfectPairing n)
  subst d
  rfl

def enumerate (n : ℕ) : List (OrientedPerfectPairing n) :=
  (templates n).map pairing

theorem mem_enumerate {n : ℕ} (p : OrientedPerfectPairing n) : p ∈ enumerate n :=
  List.mem_map.mpr ⟨normalize p,mem_templates _,normalize_exact p⟩

theorem odd_empty {n : ℕ} (hn : n%2≠0) : enumerate n=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro p hp
  have he := twice_count p
  omega

/-- Orientation and original port order occur literally in every restriction. -/
theorem restriction_entry {n : ℕ} (p : OrientedPerfectPairing n)
    (f : Signature AlgebraicComplex n) (z : Fin p.count → Bool) :
    p.restrict f z = f (fun j => if (p.ports.symm j).2
      then !(z (p.ports.symm j).1) else z (p.ports.symm j).1) := rfl

end Holant.LocalDrafts.Tractability.EOEvaluation.EOConditionCertificate.Pairings
