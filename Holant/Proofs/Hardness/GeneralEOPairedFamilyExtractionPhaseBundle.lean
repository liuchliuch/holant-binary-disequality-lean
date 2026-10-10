import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPhaseSmall

/-! The normalized residual is an actual fixed positive product of literal
minors. Inverses use cubes; no inverse signature or arithmetic oracle is added.
An original nonzero scale contributes exactly one power per emitted row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseBundle
open Holant Holant.Tractable
open GeneralEOPairedFamilyExtractionPhaseNormalization
open scoped BigOperators
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace I
export GeneralEOPairedFamilyExtractionInteraction (compose substitute_compose)
end I
namespace A
export AffinePhase (word basis origin)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {m n : ℕ}

def keep (s : Finset (Fin n)) : Fin n → Bool ⊕ Fin n := fun j => if j∈s then Sum.inr j else Sum.inl false

def evaluate {K : Type*} [CommMonoid K] (f : Signature K n)
    (ps : List (Fin n → Bool ⊕ Fin m)) (x : Fin m → Bool) : K :=
  (ps.map (fun p => f (T.substitute p x))).prod

theorem evaluate_append {K : Type*} [CommMonoid K] (f : Signature K n)
    (ps qs : List (Fin n → Bool ⊕ Fin m)) (x : Fin m → Bool) :
    evaluate f (ps++qs) x=evaluate f ps x*evaluate f qs x := by
  simp only [evaluate,List.map_append,List.prod_append]

theorem evaluate_flatten {K : Type*} [CommMonoid K] (f : Signature K n)
    (pss : List (List (Fin n → Bool ⊕ Fin m))) (x : Fin m → Bool) :
    evaluate f pss.flatten x=(pss.map (fun ps => evaluate f ps x)).prod := by
  induction pss with
  | nil => rfl
  | cons ps pss ih => simp only [List.flatten_cons,evaluate_append,List.map_cons,List.prod_cons,ih]

theorem evaluate_replicate {K : Type*} [CommMonoid K] (f : Signature K n)
    (p : Fin n → Bool ⊕ Fin m) (k : ℕ) (x : Fin m → Bool) :
    evaluate f (List.replicate k p) x=f (T.substitute p x)^k := by
  simp [evaluate]

theorem evaluate_scale {K : Type*} [CommMonoid K] (f : Signature K n)
    (c : K) (ps : List (Fin n → Bool ⊕ Fin m)) (x : Fin m → Bool) :
    evaluate (fun y => c*f y) ps x=c^ps.length*evaluate f ps x := by
  induction ps with
  | nil => simp [evaluate]
  | cons p ps ih =>
    simp only [evaluate,List.map_cons,List.prod_cons,List.length_cons] at ih ⊢
    rw [ih,pow_succ]
    ac_rfl

theorem evaluate_compose {k : ℕ} {K : Type*} [CommMonoid K] (f : Signature K n)
    (ps : List (Fin n → Bool ⊕ Fin m)) (q : Fin m → Bool ⊕ Fin k) (x : Fin k → Bool) :
    evaluate f (ps.map (fun p => I.compose p q)) x=evaluate f ps (T.substitute q x) := by
  simp only [evaluate,List.map_map,Function.comp_def,I.substitute_compose]

variable (g : Signature AlgebraicComplex n) (h0 : g (A.origin n)=1)

include h0 in
theorem keep_single (i : Fin n) (x : Fin n → Bool) : g (T.substitute (keep {i}) x)=unary g i x := by
  have he : T.substitute (keep {i}) x=if x i then A.basis i else A.origin n := by
    funext j
    by_cases hj : j=i
    · subst j
      cases h : x i <;> simp [T.substitute,keep,A.basis,A.origin,h]
    · cases h : x i <;> simp [T.substitute,keep,A.basis,A.origin,hj]
  rw [he]
  cases h : x i <;> simp [unary,h,h0]

include h0 in
theorem keep_pair (e : Edge n) (x : Fin n → Bool) :
    g (T.substitute (keep {e.val.1,e.val.2}) x)=pairTable g e ![x e.val.1,x e.val.2] := by
  have hn : e.val.1≠e.val.2 := ne_of_lt e.property
  have he : T.substitute (keep {e.val.1,e.val.2}) x=
      if x e.val.1 then (if x e.val.2 then A.word {e.val.1,e.val.2} else A.basis e.val.1)
      else (if x e.val.2 then A.basis e.val.2 else A.origin n) := by
    funext j
    by_cases ha : j=e.val.1
    · subst j
      cases h1 : x e.val.1 <;> cases h2 : x e.val.2 <;>
        simp [T.substitute,keep,A.word,A.basis,A.origin,h1,hn]
    · by_cases hb : j=e.val.2
      · subst j
        cases h1 : x e.val.1 <;> cases h2 : x e.val.2 <;>
          simp [T.substitute,keep,A.word,A.basis,A.origin,h2,ha]
      · cases h1 : x e.val.1 <;> cases h2 : x e.val.2 <;>
          simp [T.substitute,keep,A.word,A.basis,A.origin,ha,hb]
  rw [he]
  cases h1 : x e.val.1 <;> cases h2 : x e.val.2 <;> simp [pairTable,h0]

def unaryBlocks : List (List (Fin n → Bool ⊕ Fin n)) :=
  List.ofFn (fun i : Fin n => List.replicate 3 (keep {i}))

def edgeBlock (e : Edge n) : List (Fin n → Bool ⊕ Fin n) :=
  List.replicate 3 (keep {e.val.1,e.val.2})++
    List.replicate 9 (keep {e.val.1})++List.replicate 9 (keep {e.val.2})

def pairBlocks : List (List (Fin n → Bool ⊕ Fin n)) :=
  (Finset.univ : Finset (Edge n)).toList.map edgeBlock

def ports : List (Fin n → Bool ⊕ Fin n) := (fun i=>Sum.inr i)::unaryBlocks.flatten++pairBlocks.flatten

variable (hfour : ∀x,g x^4=1)

include h0 hfour in
theorem edgeBlock_value (e : Edge n) (x : Fin n → Bool) : evaluate g (edgeBlock e) x=pair g e x^3 := by
  rw [edgeBlock,evaluate_append,evaluate_append,evaluate_replicate,evaluate_replicate,evaluate_replicate,
    keep_pair g h0,keep_single g h0,keep_single g h0,pair_formula g hfour]
  ring

include h0 hfour in
theorem ports_value (x : Fin n → Bool) : evaluate g ports x=
    GeneralEOPairedFamilyExtractionPhaseNormalization.residual g x := by
  change g x*evaluate g (unaryBlocks.flatten++pairBlocks.flatten) x=_
  rw [evaluate_append,evaluate_flatten,evaluate_flatten]
  simp only [unaryBlocks,pairBlocks,List.map_ofFn,List.prod_ofFn,List.map_map,Function.comp_def,
    evaluate_replicate,keep_single g h0,edgeBlock_value g h0 hfour,Finset.prod_map_toList]
  rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseBundle
