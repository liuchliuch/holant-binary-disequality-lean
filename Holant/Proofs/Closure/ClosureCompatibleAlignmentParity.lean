import Holant.Proofs.Closure.ClosureSixPortCurrentCards

/-! Global support parity at every total arity at least three, from the
literal zero-safe ordered root deck.  This generalizes the checked six-port
argument; no common nonzero phase samples or supplied parity classifier occur. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
open Holant Holant.Tractable Holant.Projective Holant.Algebraic Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.Certificates.MatchingContractionClosure
open ClosureSixPort (Word bit parity)

variable {n : ℕ}

theorem rootMatching_cross_parityN {m : ℕ} {q : Signature ℂ n}
    (matching : q = 0 ∨ ClosureSixPort.RootMatching m q)
    (x y : Word n) (different : parity x ≠ parity y) : q x*q y = 0 := by
  rcases matching with rfl | ⟨M,mono,_,rfl⟩
  · simp
  obtain ⟨p,support⟩ := ClosureSixPort.presentation_support_parity M mono
  by_cases hx : M.tensor x = 0
  · rw [hx,zero_mul]
  by_cases hy : M.tensor y = 0
  · rw [hy,mul_zero]
  exact False.elim (different ((support x hx).trans (support y hy).symm))

def fillPairN (e : Equiv.Perm (Fin (n+2))) (a p : Bool) (x : Word n) : Word (n+2) :=
  fun i => (Fin.cons a (Fin.cons (a ^^ p) x) : Word (n+2)) (e.symm i)
def slicePairN (h : Signature ℂ (n+2)) (e : Equiv.Perm (Fin (n+2))) (p a : Bool) : Signature ℂ n :=
  fun x => h (fillPairN e a p x)
def phaseCardN (h : Signature ℂ (n+2)) (e : Equiv.Perm (Fin (n+2))) (p : Bool) (t : ℂ) : Signature ℂ n :=
  slicePairN h e p false + t • slicePairN h e p true

def OrderedRootDeckN (m : ℕ) (h : Signature ℂ (n+2)) : Prop :=
  ∀ e : Equiv.Perm (Fin (n+2)),∀ p : Bool,∀ t : ℂ,t^m=1 →
    phaseCardN h e p t = 0 ∨ ClosureSixPort.RootMatching m (phaseCardN h e p t)

theorem phaseCardN_actual (h : Signature ℂ (n+2)) (e : Equiv.Perm (Fin (n+2))) (p : Bool) (t : ℂ) :
    phaseCardN h e p t = Holant.Dihedral.EndpointParallelogram.card h e p t 1 := by
  funext x
  change h (fun i => (Fin.cons false (Fin.cons (false ^^ p) x) : Word (n+2)) (e.symm i)) +
    t*h (fun i => (Fin.cons true (Fin.cons (true ^^ p) x) : Word (n+2)) (e.symm i)) = _
  cases p <;> simp [Holant.Dihedral.EndpointParallelogram.card,
    Holant.Dihedral.EndpointParallelogram.phaseKernel,Fintype.sum_bool] <;> ring

theorem endpoint_cross_parityN {m : ℕ} (hm : 3 ≤ m) (h : Signature ℂ (n+2))
    (deck : OrderedRootDeckN m h) (e : Equiv.Perm (Fin (n+2))) (p : Bool)
    (x y : Word n) (different : parity x ≠ parity y) :
    (slicePairN h e p false x = 0 ∧ slicePairN h e p true x = 0) ∨
      (slicePairN h e p false y = 0 ∧ slicePairN h e p true y = 0) := by
  apply affine_product_zero_on_rootPolygon hm
  intro t ht
  exact rootMatching_cross_parityN (deck e p t ht) x y different

theorem endpoint_supported_parityN {m : ℕ} (hm : 3 ≤ m) (h : Signature ℂ (n+2))
    (deck : OrderedRootDeckN m h) (e : Equiv.Perm (Fin (n+2))) (p a b : Bool)
    (x y : Word n) (hx : slicePairN h e p a x ≠ 0) (hy : slicePairN h e p b y ≠ 0) :
    parity x = parity y := by
  by_contra different
  rcases endpoint_cross_parityN hm h deck e p x y different with zero | zero
  · cases a
    · exact hx zero.1
    · exact hx zero.2
  · cases b
    · exact hy zero.1
    · exact hy zero.2

def residualPairN (e : Equiv.Perm (Fin (n+2))) (w : Word (n+2)) : Word n :=
  fun i => w (e i.succ.succ)

theorem fillPairN_reconstruct (e : Equiv.Perm (Fin (n+2))) (w : Word (n+2)) :
    fillPairN e (w (e 0)) (w (e 0) ^^ w (e 1)) (residualPairN e w) = w := by
  funext i
  obtain ⟨j,rfl⟩ := e.surjective i
  simp only [fillPairN,Equiv.symm_apply_apply]
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) j
  · simp
  · simp
  · rfl

theorem parity_fillPairN (e : Equiv.Perm (Fin (n+2))) (a p : Bool) (x : Word n) :
    parity (fillPairN e a p x) = bit p+parity x := by
  have pairBit : bit a+bit (a ^^ p)=bit p := by cases a <;> cases p <;> decide
  unfold parity
  rw [← Equiv.sum_comp e (fun i => bit (fillPairN e a p x i))]
  simp only [fillPairN,Equiv.symm_apply_apply]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]
  rw [← add_assoc,pairBit]

theorem same_deleted_parityN {m : ℕ} (hm : 3 ≤ m) (h : Signature ℂ (n+2))
    (deck : OrderedRootDeckN m h) (e : Equiv.Perm (Fin (n+2)))
    (w v : Word (n+2)) (hw : h w ≠ 0) (hv : h v ≠ 0)
    (same : (w (e 0) ^^ w (e 1)) = (v (e 0) ^^ v (e 1))) : parity w = parity v := by
  let p := w (e 0) ^^ w (e 1)
  have hx : slicePairN h e p (w (e 0)) (residualPairN e w) ≠ 0 := by
    simpa only [slicePairN,p,fillPairN_reconstruct] using hw
  have hy : slicePairN h e p (v (e 0)) (residualPairN e v) ≠ 0 := by
    rw [show p = (v (e 0) ^^ v (e 1)) from same]
    simpa only [slicePairN,fillPairN_reconstruct] using hv
  have residual := endpoint_supported_parityN hm h deck e p _ _ _ _ hx hy
  rw [← fillPairN_reconstruct e w,← fillPairN_reconstruct e v,
    parity_fillPairN,parity_fillPairN,same,residual]

private theorem three_pair_disagreementsN : ∀ a b c A B C : Bool,
    (a ^^ b) ≠ (A ^^ B) → (a ^^ c) ≠ (A ^^ C) → (b ^^ c) ≠ (B ^^ C) → False := by decide

theorem supported_words_same_parityN {m : ℕ} (hm : 3 ≤ m) (large : 3 ≤ n+2)
    (h : Signature ℂ (n+2)) (deck : OrderedRootDeckN m h)
    (w v : Word (n+2)) (hw : h w ≠ 0) (hv : h v ≠ 0) : parity w = parity v := by
  by_contra different
  have pairs (e : Equiv.Perm (Fin (n+2))) :
      (w (e 0) ^^ w (e 1)) ≠ (v (e 0) ^^ v (e 1)) := by
    intro equal
    exact different (same_deleted_parityN hm h deck e w v hw hv equal)
  let third : Fin (n+2) := ⟨2,by omega⟩
  have zeroThird : (0 : Fin (n+2)) ≠ third := by
    intro equal
    have h := congrArg Fin.val equal
    change 0=2 at h
    omega
  have oneThird : (1 : Fin (n+2)) ≠ third := by
    intro equal
    have h := congrArg Fin.val equal
    have oneValue : (1 : Fin (n+2)).val=1 := by simp
    rw [oneValue] at h
    change 1=2 at h
    omega
  apply three_pair_disagreementsN (w 0) (w 1) (w third) (v 0) (v 1) (v third)
  · exact pairs (Equiv.refl _)
  · simpa only [Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne Fin.zero_ne_one zeroThird] using pairs (Equiv.swap 1 third)
  · simpa only [Equiv.trans_apply,Equiv.swap_apply_left,Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm Fin.zero_ne_one) oneThird] using
      pairs ((Equiv.swap (0 : Fin (n+2)) 1).trans (Equiv.swap 0 third))

theorem exists_global_parityN {m : ℕ} (hm : 3 ≤ m) (large : 3 ≤ n+2)
    (h : Signature ℂ (n+2)) (nonzero : h ≠ 0) (deck : OrderedRootDeckN m h) :
    ∃ p : ZMod 2,∀ w : Word (n+2),parity w ≠ p → h w = 0 := by
  obtain ⟨w,hw⟩ : ∃ w,h w ≠ 0 := by
    by_contra none
    push_neg at none
    exact nonzero (funext none)
  exact ⟨parity w,fun v different => by
    by_contra hv
    exact different (supported_words_same_parityN hm large h deck v w hv hw)⟩

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))

/-- The full generic ordered root deck comes from the actual CURRENT source
deck and its exact ORIGINAL-field keys/scalars; it is not a final input oracle. -/
theorem current_ordered_root_deckN (h : Signature (OI.K G) (n+2))
    (stable : ∀ g ∈ rawDeck P.family torsion h,MatchingOrZero (actualTransfers P.family) g) :
    OrderedRootDeckN N.m (RingHomRealization.mapSignature (ClosureSixPort.sourceComplex G) h) := by
  intro e p t ht
  let key := DeckContraction.orderedKey P.family torsion e
    (ClosureSixPort.cardIndex G P torsion N p t ht).key
  have matching := ClosureSixPort.current_matching_map G P torsion N
    (rawCard P.family torsion h key) (stable _ (Or.inr ⟨key,rfl⟩))
  have bridge := ClosureSixPort.ordered_card_raw_scalar G P torsion N h e p t ht
  change RingHomRealization.mapSignature (ClosureSixPort.sourceComplex G)
    (rawCard P.family torsion h key) = _ at bridge
  rw [bridge,← phaseCardN_actual] at matching
  exact ClosureSixPort.rootMatchingOrZero_unscale _ (ClosureSixPort.cardScalar_nonzero G P torsion N p t ht) matching

include N in
theorem current_global_support_parity (large : 3 ≤ n+2) (h : Signature (OI.K G) (n+2))
    (nonzero : h ≠ 0)
    (stable : ∀ g ∈ rawDeck P.family torsion h,MatchingOrZero (actualTransfers P.family) g) :
    ∃ p : ZMod 2,∀ w : Word (n+2),parity w ≠ p → h w = 0 := by
  have mappedNonzero : RingHomRealization.mapSignature (ClosureSixPort.sourceComplex G) h ≠ 0 := by
    intro zero
    apply nonzero
    funext w
    have hzero := congrFun zero w
    exact (map_eq_zero _).mp hzero
  obtain ⟨p,support⟩ := exists_global_parityN N.range large _ mappedNonzero
    (current_ordered_root_deckN G P torsion N h stable)
  exact ⟨p,fun w different => (map_eq_zero _).mp (support w different)⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
