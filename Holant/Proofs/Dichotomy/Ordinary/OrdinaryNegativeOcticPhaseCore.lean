import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPhaseOccurrences

/-! Positive octic phase normalization. Seventh powers remove the actual
unary and binary phases, and all literal free-port counts are multiples of
eight. The trivial residual retains an explicit factorization, with no
tractability assertion. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeOcticPhaseCore
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open scoped BigOperators
namespace A
export AffinePhase (word basis origin)
end A
namespace N
export GeneralEOPairedFamilyExtractionPhaseNormalization (Edge unary pairTable)
end N
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace B
export GeneralEOPairedFamilyExtractionPhaseBundle
  (evaluate evaluate_append evaluate_flatten evaluate_replicate evaluate_scale
    evaluate_compose keep keep_single keep_pair)
end B
namespace O
export GeneralEOPairedFamilyExtractionPhaseOccurrences
  (occurrences occurrences_append occurrences_cons occurrences_flatten occurrences_replicate
    keep_count incident_count occurrences_compose dvd_occurrences_compose)
end O
namespace S
export GeneralEOPairedFamilyExtractionPhaseSmall (pair_index_eq)
end S
namespace I
export GeneralEOPairedFamilyExtractionInteraction (compose)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768

variable {n : ℕ} (g : Signature AlgebraicComplex n)

def interaction (e : N.Edge n) : AlgebraicComplex :=
  g (A.word {e.val.1,e.val.2})*g (A.basis e.val.1)^7*g (A.basis e.val.2)^7

def pair (e : N.Edge n) (x : Fin n → Bool) : AlgebraicComplex :=
  if x e.val.1 && x e.val.2 then interaction g e else 1

def lowOrder (x : Fin n → Bool) : AlgebraicComplex :=
  (∏i,N.unary g i x)*(∏e : N.Edge n,pair g e x)

def residual : Signature AlgebraicComplex n := fun x => g x*lowOrder g x^7

variable (h0 : g (A.origin n)=1) (height : ∀x,g x^8=1)

include height in
theorem unary_eight (i : Fin n) (x : Fin n → Bool) : N.unary g i x^8=1 := by
  cases h : x i <;> simp [N.unary,h,height]

include height in
theorem interaction_eight (e : N.Edge n) : interaction g e^8=1 := by
  simp only [interaction,mul_pow]
  rw [pow_right_comm (g (A.basis e.val.1)) 7 8,pow_right_comm (g (A.basis e.val.2)) 7 8]
  rw [height,height,height]
  norm_num

include height in
theorem pair_eight (e : N.Edge n) (x : Fin n → Bool) : pair g e x^8=1 := by
  unfold pair
  split_ifs
  · exact interaction_eight g height e
  · norm_num

include height in
theorem lowOrder_eight (x : Fin n → Bool) : lowOrder g x^8=1 := by
  unfold lowOrder
  rw [mul_pow,←Finset.prod_pow,←Finset.prod_pow]
  simp [unary_eight g height,pair_eight g height]

include height in
theorem residual_eight (x : Fin n → Bool) : residual g x^8=1 := by
  rw [residual,mul_pow,pow_right_comm, height,lowOrder_eight g height]
  norm_num

include height in
theorem pair_formula (e : N.Edge n) (x : Fin n → Bool) :
    pair g e x=N.pairTable g e ![x e.val.1,x e.val.2]*
      N.unary g e.val.1 x^7*N.unary g e.val.2 x^7 := by
  have ha := height (A.basis e.val.1)
  have hb := height (A.basis e.val.2)
  cases h1 : x e.val.1 <;> cases h2 : x e.val.2
  · simp [pair,N.pairTable,N.unary,h1,h2]
  · simpa [pair,N.pairTable,N.unary,h1,h2,←pow_succ'] using hb.symm
  · simpa [pair,N.pairTable,N.unary,h1,h2,←pow_succ'] using ha.symm
  · simp [pair,N.pairTable,N.unary,interaction,h1,h2]

include height in
theorem factorization_of_residual_one (hres : ∀x,residual g x=1) :
    ∀x,g x=lowOrder g x := by
  intro x
  calc
    g x=g x*lowOrder g x^8 := by rw [lowOrder_eight g height,mul_one]
    _=(g x*lowOrder g x^7)*lowOrder g x := by ring
    _=lowOrder g x := by rw [show g x*lowOrder g x^7=1 from hres x,one_mul]

include h0 in
theorem residual_empty : residual g (A.word ∅)=1 := by
  simp [residual,lowOrder,N.unary,pair,A.word,h0]

theorem pair_single (e : N.Edge n) (i : Fin n) : pair g e (A.word {i})=1 := by
  have hn : ¬(e.val.1=i ∧ e.val.2=i) := by
    rintro ⟨ha,hb⟩
    have hh := e.property
    rw [ha,hb] at hh
    exact (lt_irrefl i) hh
  simp [pair,A.word,hn]

theorem unary_single_product (i : Fin n) :
    (∏j,N.unary g j (A.word {i}))=g (A.basis i) := by
  have he (j : Fin n) : N.unary g j (A.word {i})=
      if j=i then g (A.basis i) else 1 := by
    by_cases hj : j=i
    · subst j; simp [N.unary,A.word]
    · simp [N.unary,A.word,hj]
  simp only [he,Finset.prod_ite_eq',Finset.mem_univ,ite_true]

include height in
theorem residual_single (i : Fin n) : residual g (A.word {i})=1 := by
  have hp : (∏e : N.Edge n,pair g e (A.word {i}))=1 := by
    apply Finset.prod_eq_one
    intro e _
    exact pair_single g e i
  rw [residual,lowOrder,unary_single_product,hp,mul_one,AffinePhase.word_singleton]
  calc
    _=g (A.basis i)^8 := by ring
    _=1 := height _

theorem pair_pair (a b : Fin n) (hab : a<b) (e : N.Edge n) :
    pair g e (A.word {a,b})=if e=⟨(a,b),hab⟩ then interaction g ⟨(a,b),hab⟩ else 1 := by
  by_cases he : e=⟨(a,b),hab⟩
  · subst e; simp [pair,A.word]
  · rw [ite_eq_right he]
    have hn : ¬(e.val.1=a ∨ e.val.1=b) ∨ ¬(e.val.2=a ∨ e.val.2=b) := by
      by_contra hh
      push Not at hh
      exact he (S.pair_index_eq a b hab e hh.1 hh.2)
    rcases hn with hn|hn <;> simp [pair,A.word,hn]

theorem unary_pair_product (a b : Fin n) (hab : a≠b) :
    (∏j,N.unary g j (A.word {a,b}))=g (A.basis a)*g (A.basis b) := by
  have he (j : Fin n) : N.unary g j (A.word {a,b})=
      (if j=a then g (A.basis a) else 1)*(if j=b then g (A.basis b) else 1) := by
    by_cases ha : j=a <;> by_cases hb : j=b
    · exact False.elim (hab (ha.symm.trans hb))
    · subst j; simp [N.unary,A.word,hb]
    · subst j; simp [N.unary,A.word,ha]
    · simp [N.unary,A.word,ha,hb]
  simp only [he,Finset.prod_mul_distrib,Finset.prod_ite_eq',Finset.mem_univ,ite_true]

include height in
theorem lowOrder_pair (a b : Fin n) (hab : a<b) :
    lowOrder g (A.word {a,b})=g (A.word {a,b}) := by
  have hp : (∏e : N.Edge n,pair g e (A.word {a,b}))=interaction g ⟨(a,b),hab⟩ := by
    simp only [pair_pair g a b hab,Finset.prod_ite_eq',Finset.mem_univ,ite_true]
  rw [lowOrder,unary_pair_product g a b (ne_of_lt hab),hp]
  unfold interaction
  calc
    _=g (A.word {a,b})*g (A.basis a)^8*g (A.basis b)^8 := by ring
    _=g (A.word {a,b}) := by rw [height,height]; ring

include height in
theorem residual_pair (a b : Fin n) (hab : a<b) : residual g (A.word {a,b})=1 := by
  rw [residual,lowOrder_pair g height a b hab]
  calc
    _=g (A.word {a,b})^8 := by ring
    _=1 := height _

include h0 height in
theorem residual_small (s : Finset (Fin n)) (hs : s.card≤2) : residual g (A.word s)=1 := by
  have hh : s.card=0 ∨ s.card=1 ∨ s.card=2 := by omega
  rcases hh with hh|hh|hh
  · obtain rfl := Finset.card_eq_zero.mp hh
    exact residual_empty g h0
  · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hh
    exact residual_single g height i
  · obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hh
    rcases lt_or_gt_of_ne hab with h|h
    · exact residual_pair g height a b h
    · rw [Finset.pair_comm]
      exact residual_pair g height b a h

variable {g}

def unaryBlocks : List (List (Fin n → Bool ⊕ Fin n)) :=
  List.ofFn (fun i : Fin n => List.replicate 7 (B.keep {i}))

def edgeBlock (e : N.Edge n) : List (Fin n → Bool ⊕ Fin n) :=
  List.replicate 7 (B.keep {e.val.1,e.val.2})++
    List.replicate 49 (B.keep {e.val.1})++List.replicate 49 (B.keep {e.val.2})

def pairBlocks : List (List (Fin n → Bool ⊕ Fin n)) :=
  (Finset.univ : Finset (N.Edge n)).toList.map edgeBlock

def ports : List (Fin n → Bool ⊕ Fin n) :=
  (fun i => Sum.inr i)::unaryBlocks.flatten++pairBlocks.flatten

variable (g)
include h0 height in
theorem edgeBlock_value (e : N.Edge n) (x : Fin n → Bool) :
    B.evaluate g (edgeBlock e) x=pair g e x^7 := by
  rw [edgeBlock,B.evaluate_append,B.evaluate_append,B.evaluate_replicate,B.evaluate_replicate,
    B.evaluate_replicate,B.keep_pair g h0,B.keep_single g h0,B.keep_single g h0,pair_formula g height]
  ring

include h0 height in
theorem ports_value (x : Fin n → Bool) : B.evaluate g ports x=residual g x := by
  change g x*B.evaluate g (unaryBlocks.flatten++pairBlocks.flatten) x=_
  rw [B.evaluate_append,B.evaluate_flatten,B.evaluate_flatten]
  simp only [unaryBlocks,pairBlocks,List.map_ofFn,List.prod_ofFn,List.map_map,Function.comp_def,
    B.evaluate_replicate,B.keep_single g h0,edgeBlock_value g h0 height,Finset.prod_map_toList]
  simp only [residual,lowOrder,mul_pow,←Finset.prod_pow]

/-- Seven inverse unary copies plus the base occurrence. -/
theorem occurrences_unaryBlocks (j : Fin n) : O.occurrences unaryBlocks.flatten j=7 := by
  have hu (i : Fin n) : O.occurrences (List.replicate 7 (B.keep {i})) j=
      7*(if j=i then 1 else 0) := by
    rw [O.occurrences_replicate,O.keep_count]
    simp
  rw [O.occurrences_flatten]
  unfold unaryBlocks
  rw [List.map_ofFn,List.sum_ofFn]
  simp only [Function.comp_def]
  simp_rw [hu]
  rw [←Finset.mul_sum]
  simp

theorem occurrences_edgeBlock (e : N.Edge n) (j : Fin n) :
    O.occurrences (edgeBlock e) j=if j=e.val.1 ∨ j=e.val.2 then 56 else 0 := by
  have hne : e.val.1≠e.val.2 := ne_of_lt e.property
  simp only [edgeBlock,O.occurrences_append,O.occurrences_replicate,O.keep_count]
  by_cases h1 : j=e.val.1
  · subst j; simp [hne]
  · by_cases h2 : j=e.val.2
    · subst j; simp [hne.symm]
    · simp [h1,h2]

/-- Exact raw incidence, before identifying or pinning original coordinates. -/
theorem occurrences_ports (j : Fin n) : O.occurrences (ports (n := n)) j=8+56*(n-1) := by
  have hh : O.occurrences (ports (n := n)) j=
      8+56*∑e : N.Edge n,if j=e.val.1 ∨ j=e.val.2 then 1 else 0 := by
    rw [ports,O.occurrences_append,O.occurrences_cons,occurrences_unaryBlocks,O.occurrences_flatten]
    simp only [pairBlocks,List.map_map,Function.comp_def,occurrences_edgeBlock,Finset.sum_map_toList]
    simp only [Sum.inr.injEq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [Finset.mul_sum]
    simp only [mul_ite,mul_one,mul_zero]
  rw [hh,O.incident_count]

/-- Exact incidence after arbitrary ternary identification and pinning. -/
theorem occurrences_ports_compose {m : ℕ} (p : Fin n → Bool ⊕ Fin m) (j : Fin m) :
    O.occurrences (ports.map (fun q => I.compose q p)) j=
      (8+56*(n-1))*∑i : Fin n,if p i=Sum.inr j then 1 else 0 := by
  rw [O.occurrences_compose]
  simp_rw [occurrences_ports]
  rw [←Finset.sum_mul,Nat.mul_comm]

theorem eight_dvd_occurrences_ports_compose {m : ℕ} (p : Fin n → Bool ⊕ Fin m) (j : Fin m) :
    8 ∣ O.occurrences (ports.map (fun q => I.compose q p)) j := by
  rw [occurrences_ports_compose]
  apply dvd_mul_of_dvd_left
  exact dvd_add (dvd_refl 8) (dvd_mul_of_dvd_left (by decide : 8 ∣ 56) _)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeOcticPhaseCore
end
