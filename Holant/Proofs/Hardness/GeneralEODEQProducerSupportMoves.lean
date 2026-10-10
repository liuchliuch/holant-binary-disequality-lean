import Holant.Proofs.Hardness.GeneralEODEQProducerSupportBasic
import Holant.Proofs.Hardness.GeneralEODEQProducerCore

/-! A finite descent on odd affine combinations. The outer induction removes
 two rows; the inner induction strictly reduces their active coordinates. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQProducerSupportMoves
open Holant Holant.Tractable GeneralEODEQProducerSupportBasic
namespace C
export GeneralEODEQProducerCore (Pair Isolated)
end C
namespace D
export GeneralEOPhaseExtractionDistance (distance)
end D
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {f : Signature AlgebraicComplex n}

/-- The interval descent supplies precisely one valid zero-moving operation.
This reusable induction lemma states all its finite combinatorial requirements. -/
theorem positive_pure_of_descent
    (he : Signature.CentralSupport f)
    (hs : EONegativeWitness.Supports .positive ⟨n,f⟩)
    (hd : ∀ (a b δ : Fin n → Bool), f a ≠ 0 → f b ≠ 0 →
      charge δ < charge (tripleXor δ a b) →
      ∃ i j, Nonempty (TwoFlip f i j) ∧ δ i = false ∧ δ j = false ∧
        a i ≠ b i ∧ a j ≠ b j) : Pure .positive f := by
  have hmain : ∀ k : ℕ, ∀ xs : List (Fin n → Bool), xs.length = k →
      Odd xs.length → (∀ x ∈ xs, f x ≠ 0) → 0 ≤ charge (xorList xs) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k outer =>
      have hinner : ∀ m : ℕ, ∀ xs : List (Fin n → Bool), xs.length = k →
          (active xs).card = m → Odd xs.length →
          (∀ x ∈ xs, f x ≠ 0) → 0 ≤ charge (xorList xs) := by
        intro m
        induction m using Nat.strong_induction_on with
        | h m inner =>
          intro xs hlen hm ho hsup
          by_contra hn
          have hneg : charge (xorList xs) < 0 := by omega
          cases xs with
          | nil => simp at ho
          | cons a tail =>
            cases tail with
            | nil =>
              have ha : f a ≠ 0 := hsup a (by simp)
              have hz : xorList [a] = a := by funext i; simp [xorList]
              rw [hz, central_charge he ha] at hneg
              omega
            | cons b rest =>
              have ha : f a ≠ 0 := hsup a (by simp)
              have hb : f b ≠ 0 := hsup b (by simp)
              have hrest : 0 ≤ charge (xorList rest) := by
                apply outer rest.length (by simp only [List.length_cons] at hlen; omega) rest rfl
                · rw [Nat.odd_iff] at ho ⊢
                  simp only [List.length_cons] at ho
                  omega
                · intro x hx
                  exact hsup x (by simp [hx])
              have hcancel : tripleXor (xorList (a :: b :: rest)) a b = xorList rest := by
                funext i
                simp only [xorList_cons, tripleXor]
                cases a i <;> cases b i <;> cases xorList rest i <;> rfl
              have himprove : charge (xorList (a :: b :: rest)) <
                  charge (tripleXor (xorList (a :: b :: rest)) a b) := by
                rw [hcancel]
                omega
              obtain ⟨i,j,⟨T⟩,hi,hj,hai,haj⟩ := hd a b _ ha hb himprove
              have hactive : ∀ q, a q ≠ b q → q ∈ active (a :: b :: rest) := by
                intro q hq
                apply (mem_active _ _).mpr
                cases haq : a q <;> cases hbq : b q
                · exact (hq (haq.trans hbq.symm)).elim
                · exact ⟨b,by simp,hbq⟩
                · exact ⟨a,by simp,haq⟩
                · exact (hq (haq.trans hbq.symm)).elim
              have hlt := active_move_lt i j (a :: b :: rest) (hactive i hai) (hactive j haj)
              have hout : 0 ≤ charge (xorList ((a :: b :: rest).map (move i j))) := by
                apply inner (active ((a :: b :: rest).map (move i j))).card (by omega)
                  ((a :: b :: rest).map (move i j))
                · simpa using hlen
                · rfl
                · simpa using ho
                · intro x hx
                  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
                  exact T.move_supported he hs (hsup y hy)
              rw [xorList_move i j T.distinct, move_eq_self hi] at hout
              omega
      intro xs hlen ho hsup
      exact hinner (active xs).card xs hlen rfl ho hsup
  intro xs ho hsup
  simpa [EOSign.value] using hmain xs.length xs rfl ho hsup

/-- The Boolean complement of an ordered word. -/
def complement (x : Fin n → Bool) : Fin n → Bool := fun i => !(x i)

@[simp] theorem complement_complement (x : Fin n → Bool) :
    complement (complement x) = x := by funext i; simp [complement]

@[simp] theorem charge_complement (x : Fin n → Bool) :
    charge (complement x) = -charge x := charge_compl x

theorem complement_triple (a b c : Fin n → Bool) :
    tripleXor (complement a) (complement b) (complement c) =
      complement (tripleXor a b c) := by
  funext i
  change Bool.xor (Bool.xor (!(a i)) (!(b i))) (!(c i)) =
    Bool.not (Bool.xor (Bool.xor (a i) (b i)) (c i))
  cases a i <;> cases b i <;> cases c i <;> rfl

/-- Reflect the signature through the centre of its Boolean cube. -/
def dual (f : Signature AlgebraicComplex n) : Signature AlgebraicComplex n :=
  fun x => f (complement x)

@[simp] theorem dual_dual (f : Signature AlgebraicComplex n) : dual (dual f) = f := by
  funext x
  simp [dual]

theorem dual_central (he : Signature.CentralSupport f) : Signature.CentralSupport (dual f) := by
  intro x hx
  apply he
  have hw := weight_compl_add x
  change 2 * weight (fun i => !(x i)) ≠ n
  omega

theorem dual_supports (hs : EONegativeWitness.Supports .negative ⟨n,f⟩) :
    EONegativeWitness.Supports .positive ⟨n,dual f⟩ := by
  intro a b c ha hb hc
  have h := hs (complement a) (complement b) (complement c) ha hb hc
  rw [complement_triple] at h
  simpa [dual, charge_complement, EOSign.value] using h

/-- Complementing an odd number of rows complements their affine sum. -/
theorem xorList_complement_odd (xs : List (Fin n → Bool)) (ho : Odd xs.length) :
    xorList (xs.map complement) = complement (xorList xs) := by
  have hall : ∀ xs : List (Fin n → Bool),
      xorList (xs.map complement) =
        (fun i => Bool.xor (decide (Odd xs.length)) (xorList xs i)) := by
    intro ys
    induction ys with
    | nil => simp [xorList]
    | cons y ys ih =>
      funext i
      simp only [List.map_cons, xorList_cons, ih, complement, List.length_cons]
      have hp : decide (Odd (ys.length + 1)) = !(decide (Odd ys.length)) := by
        by_cases h : Odd ys.length
        · have hn : ¬Odd (ys.length + 1) := by
            rw [Nat.odd_iff] at h
            rw [Nat.odd_iff]
            omega
          simp [h,hn]
        · have hy : Odd (ys.length + 1) := by
            rw [Nat.odd_iff] at h ⊢
            omega
          simp [h,hy]
      rw [hp]
      cases y i <;> cases decide (Odd ys.length) <;> cases xorList ys i <;> rfl
  rw [hall]
  funext i
  change Bool.xor (decide (Odd xs.length)) (xorList xs i) = Bool.not (xorList xs i)
  simp [ho]

theorem negative_pure_of_dual (hp : Pure .positive (dual f)) : Pure .negative f := by
  intro xs ho hsup
  have h := hp (xs.map complement) (by simpa using ho) (by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    simpa [dual] using hsup y hy)
  rw [xorList_complement_odd xs ho, charge_complement] at h
  simpa [EOSign.value] using h

/-- Isolated intervals and their distance survive Boolean complementation. -/
def pair_of_dual (P : C.Pair (dual f)) : C.Pair f where
  left := complement P.left
  right := complement P.right
  left_supported := P.left_supported
  right_supported := P.right_supported
  distant := by
    have hdist : D.distance (complement P.left) (complement P.right) =
        D.distance P.left P.right := by
      unfold D.distance
      apply Finset.sum_congr rfl
      intro i _
      simp [complement]
    rw [hdist]
    exact P.distant
  isolated := by
    intro x hx hfix
    have hcx : dual f (complement x) ≠ 0 := by simpa [dual] using hx
    have hfix' : ∀ i, P.left i = P.right i → complement x i = P.left i := by
      intro i hi
      have hh := hfix i (by simp [complement, hi])
      change Bool.not (x i) = P.left i
      change x i = !(P.left i) at hh
      simp [hh]
    rcases P.isolated (complement x) hcx hfix' with h|h
    · left
      have hh := congrArg complement h
      simpa using hh
    · right
      have hh := congrArg complement h
      simpa using hh

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQProducerSupportMoves
