axiom Class : Type

variable {x y z w : Class}

axiom In : Class → Class → Prop
axiom Classify : (Class → Prop) → Class

instance : Membership Class Class where mem := In

@[ext] axiom Class.eq : (∀ z, z ∈ x ↔ z ∈ y) → x = y

def Ensemble (x : Class) := ∃ (y : Class), x ∈ y

axiom Class.classify {P : Class → Prop} : x ∈ Classify P ↔ (Ensemble x) ∧ (P x)

theorem Ensemble.intro (p : x ∈ y) : Ensemble x := Exists.intro y p

noncomputable instance : Union Class where
  union (x y : Class) := Classify fun z => z ∈ x ∨ z ∈ y
  
noncomputable instance : Inter Class where
  inter (x y : Class) := Classify fun z => z ∈ x ∧ z ∈ y
  
theorem Union.dist : z ∈ x ∪ y ↔ (z ∈ x) ∨ (z ∈ y) := Iff.intro
  (fun h => (Class.classify.mp h).right)
  (fun h =>
    have h1 := Class.classify.mpr
    h.elim
      (fun zsx => h1 ⟨Ensemble.intro zsx, Or.inl zsx⟩)
      (fun zsy => h1 ⟨Ensemble.intro zsy, Or.inr zsy⟩)
  )

def Union.split : z ∈ x ∪ y → (z ∈ x) ∨ (z ∈ y) := Iff.mp Union.dist
def Union.intro : (z ∈ x) ∨ (z ∈ y) → z ∈ x ∪ y := Iff.mpr Union.dist

theorem Inter.dist : z ∈ x ∩ y ↔ (z ∈ x) ∧ (z ∈ y) := Iff.intro
  (fun h => (Class.classify.mp h).right)
  (fun h => h.elim (fun zsx zsy => Class.classify.mpr ⟨Ensemble.intro zsx, ⟨zsx, zsy⟩⟩))

def Inter.split : z ∈ x ∩ y → (z ∈ x) ∧ (z ∈ y) := Iff.mp Inter.dist
def Inter.intro : (z ∈ x) ∧ (z ∈ y) → z ∈ x ∩ y := Iff.mpr Inter.dist

theorem Union.idem : y ∈ x ∪ x ↔ y ∈ x := Iff.intro (fun h => (Union.split h).elim id id) (fun h => Union.intro (Or.inl h))
theorem Union.idem_eq : x ∪ x = x := Class.eq fun _ => Union.idem

theorem Inter.idem : y ∈ x ∩ x ↔ y ∈ x := Iff.intro (fun h => (Inter.split h).left) (fun h => Inter.intro ⟨h, h⟩)
theorem Inter.idem_eq : x ∩ x = x := Class.eq fun _ => Inter.idem

@[symm] theorem Union.comm : z ∈ x ∪ y → z ∈ y ∪ x := fun h => Union.intro (Union.split h).symm
theorem Union.comm_eq : x ∪ y = y ∪ x := Class.eq fun _ => Iff.intro Union.comm Union.comm

@[symm] theorem Inter.comm : z ∈ x ∩ y → z ∈ y ∩ x := fun h => Inter.intro (Inter.split h).symm
theorem Inter.comm_eq : x ∩ y = y ∩ x := Class.eq fun _ => Iff.intro Inter.comm Inter.comm

private theorem Union.assoc_oneshot : w ∈ (x ∪ y) ∪ z → w ∈ x ∪ (y ∪ z) := fun h => Or.elim (Union.split h)
  (fun wsxy => Or.elim (Union.split wsxy) (fun wsx => Union.intro (Or.inl wsx)) (fun wsy => Union.intro (Or.inr (Union.intro (Or.inl wsy)))))
  (fun wsz => Union.intro (Or.inr (Union.intro (Or.inr wsz))))

private theorem Inter.assoc_oneshot : w ∈ (x ∩ y) ∩ z → w ∈ x ∩ (y ∩ z) := fun h =>
  have ⟨wsxy, wsz⟩ := Inter.split h; have ⟨wsx, wsy⟩ := Inter.split wsxy
  Inter.intro ⟨wsx, Inter.intro ⟨wsy, wsz⟩⟩

theorem Union.assoc : w ∈ (x ∪ y) ∪ z ↔ w ∈ x ∪ (y ∪ z) := Iff.intro
  Union.assoc_oneshot
  fun h => Union.comm (Union.assoc_oneshot (Union.comm (Union.assoc_oneshot (Union.comm h))))
theorem Union.assoc_eq : (x ∪ y) ∪ z = x ∪ (y ∪ z) := Class.eq fun _ => Union.assoc

theorem Inter.assoc : w ∈ (x ∩ y) ∩ z ↔ w ∈ x ∩ (y ∩ z) := Iff.intro
  Inter.assoc_oneshot
  fun h => Inter.comm (Inter.assoc_oneshot (Inter.comm (Inter.assoc_oneshot (Inter.comm h))))
theorem Inter.assoc_eq : (x ∩ y) ∩ z = x ∩ (y ∩ z) := Class.eq fun _ => Inter.assoc

theorem Inter.dist_union : w ∈ x ∩ (y ∪ z) ↔ w ∈ (x ∩ y) ∪ (x ∩ z) := Iff.intro
  (fun h => have ⟨wsx, wsyoz⟩ := Inter.split h
    Union.intro
    ((Union.split wsyoz).elim (fun wsy => Or.inl (Inter.intro ⟨wsx, wsy⟩))
    (fun wsz => Or.inr (Inter.intro ⟨wsx, wsz⟩))))
  (fun h => Or.elim (Union.split h)
    (fun h => have ⟨wsx, wsy⟩ := Inter.split h; Inter.intro ⟨wsx, Union.intro (Or.inl wsy)⟩)
    (fun h => have ⟨wsx, wsz⟩ := Inter.split h; Inter.intro ⟨wsx, Union.intro (Or.inr wsz)⟩))
theorem Inter.dist_union_eq : x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z) := Class.eq fun _ => Inter.dist_union

def Inter.unfold_union : w ∈ x ∩ (y ∪ z) → w ∈ (x ∩ y) ∪ (x ∩ z) := Iff.mp Inter.dist_union
def Union.fold_inter : w ∈ (x ∩ y) ∪ (x ∩ z) → w ∈ x ∩ (y ∪ z) := Iff.mpr Inter.dist_union

theorem Union.dist_inter : w ∈ x ∪ (y ∩ z) ↔ w ∈ (x ∪ y) ∩ (x ∪ z) := Iff.intro
  (fun h => Or.elim (Union.split h)
    (fun wsx => Inter.intro ⟨Union.intro (Or.inl wsx), Union.intro (Or.inl wsx)⟩)
    (fun h => have ⟨wsy, wsz⟩ := Inter.split h; Inter.intro ⟨Union.intro (Or.inr wsy), Union.intro (Or.inr wsz)⟩))
  (fun h => have ⟨h1, h2⟩ := Inter.split h
    match (Union.split h1), (Union.split h2) with
    | Or.inl wsx, _ | _, Or.inl wsx => Union.intro (Or.inl wsx)
    | Or.inr wsy, Or.inr wsz => Union.intro (Or.inr (Inter.intro ⟨wsy, wsz⟩)))
theorem Union.dist_inter_eq : x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z) := Class.eq fun _ => Union.dist_inter

def Union.unfold_inter : w ∈ x ∪ (y ∩ z) → w ∈ (x ∪ y) ∩ (x ∪ z) := Iff.mp Union.dist_inter
def Inter.fold_union : w ∈ (x ∪ y) ∩ (x ∪ z) → w ∈ x ∪ (y ∩ z):= Iff.mpr Union.dist_inter

noncomputable instance : Complement Class where
  complement x := Classify fun y => y ∉ x

theorem Complement.compl_compl : y ∈ ~~~(~~~x) ↔ y ∈ x := Iff.intro
  (fun h =>
    have ⟨ensy, (h1 : y ∉ ~~~x)⟩ := Class.classify.mp h
    Classical.byContradiction fun fake : y ∉ x => h1 (Class.classify.mpr ⟨ensy, fake⟩))
  (fun h =>
    have h1 : y ∉ ~~~x := Classical.byContradiction fun fake : ¬¬ y ∈ ~~~x =>
      have fake : y ∈ ~~~x := Classical.not_not.mp fake
      have ⟨_, (h2 : y ∉ x)⟩ := Class.classify.mp fake
      h2 h;
    Classical.byContradiction fun fake : y ∉ ~~~(~~~x) =>
      have ensy : Ensemble y := ⟨x, h⟩
      fake (Class.classify.mpr ⟨ensy, h1⟩))
theorem Complement.compl_compl_eq : ~~~(~~~x) = x := Class.eq fun _ => Complement.compl_compl

def Complement.reduce : y ∈ ~~~(~~~x) → y ∈ x := Iff.mp Complement.compl_compl

theorem Union.de_morgan : z ∈ ~~~(x ∪ y) ↔ z ∈ ~~~x ∩ ~~~y := Iff.intro
  (fun h =>
    have ⟨ensz, (h1 : z ∉ x ∪ y)⟩ := Class.classify.mp h
    have ⟨(znx : z ∉ x), (zny : z ∉ y)⟩ := not_or.mp (Not.imp h1 Union.intro)
    Inter.intro ⟨Class.classify.mpr ⟨ensz, znx⟩, Class.classify.mpr ⟨ensz, zny⟩⟩)
  (fun h =>
    have ⟨zcx, zcy⟩ := Inter.split h
    have ⟨ensz, znx⟩ := Class.classify.mp zcx
    have h1 := not_or.mpr ⟨znx, And.right (Class.classify.mp zcy)⟩
    have h2 : z ∉ x ∪ y := Not.intro fun fake => h1 (Union.split fake)
    Class.classify.mpr ⟨ensz, h2⟩)
theorem Union.de_morgan_eq : ~~~(x ∪ y) = ~~~x ∩ ~~~y := Class.eq fun _ => Union.de_morgan

theorem Inter.de_morgan : z ∈ ~~~(x ∩ y) ↔ z ∈ ~~~x ∪ ~~~y := Iff.intro
  (fun h =>
    have ⟨ensz, (h1 : z ∉ x ∩ y)⟩ := Class.classify.mp h
    Union.intro (Or.imp 
      (fun h2 => Class.classify.mpr ⟨ensz, h2⟩)
      (fun h2 => Class.classify.mpr ⟨ensz, h2⟩)
      (Classical.not_and_iff_not_or_not.mp (Not.imp h1 Inter.intro))
    ))
  (fun h =>
    have h1 := Or.imp
      (fun c => Class.classify.mp c)
      (fun c => Class.classify.mp c)
      (Union.split h)
    have h2 : z ∉ x ∩ y := Classical.byContradiction fun fake =>
      have ⟨zsx, zsy⟩ := Inter.split (Classical.not_not.mp fake)
      match h1 with
      | Or.inl ⟨_, znx⟩ => znx zsx
      | Or.inr ⟨_, zny⟩ => zny zsy
    Class.classify.mpr ⟨⟨(~~~x ∪ ~~~y), h⟩, h2⟩)
theorem Inter.de_morgan_eq : ~~~(x ∩ y) = ~~~x ∪ ~~~y := Class.eq fun _ => Inter.de_morgan

noncomputable instance : Sub Class where
  sub (x y) := x ∩ ~~~y

theorem Sub.intro : z ∈ x → z ∉ y → z ∈ x - y := fun h1 h2 =>
  Inter.intro ⟨h1, Class.classify.mpr ⟨⟨x, h1⟩, h2⟩⟩

theorem Sub.split : z ∈ x - y → z ∈ x ∧ z ∉ y := fun h =>
  And.imp_right (fun h1 => And.right (Class.classify.mp h1)) (Inter.split h)

theorem Sub.iff_and : z ∈ x - y ↔ z ∈ x ∧ z ∉ y :=
  Iff.intro Sub.split fun h => Sub.intro h.left h.right

@[symm] theorem Sub.inter_assoc : w ∈ x ∩ (y - z) ↔ w ∈ (x ∩ y) - z := Inter.assoc.symm
theorem Sub.inter_assoc_eq : x ∩ (y - z) = (x ∩ y) - z := Class.eq fun _ => Sub.inter_assoc

theorem Sub.elim_union : z ∈ x ∪ y - x → z ∈ y := fun h => have ⟨h1, h2⟩ := Sub.split h; (Union.split h1).resolve_left h2
theorem Sub.elim_union' : z ∈ x ∪ y - y → z ∈ x := fun h => have ⟨h1, h2⟩ := Sub.split h; (Union.split h1).resolve_right h2

noncomputable instance : EmptyCollection Class where
  emptyCollection := Classify fun x => x ≠ x

noncomputable def Φ : Class := ∅

theorem Class.not_in_empty : x ∉ Φ := Not.intro fun fake => (Class.classify.mp fake).right rfl

theorem Sub.elim_empty : y ∈ x - Φ ↔ y ∈ x := Iff.intro
  (fun h => have ⟨h1, _⟩ := Sub.split h; h1)
  (fun h => Sub.intro h Class.not_in_empty)
theorem Sub.elim_empty_eq : x - Φ = x := Class.eq fun _ => Sub.elim_empty

theorem Union.elim_empty : y ∈ Φ ∪ x ↔ y ∈ x := Iff.intro
  (fun h => Or.resolve_left (Union.split h) Class.not_in_empty)
  (fun h => Union.intro (Or.inr h))
theorem Union.elim_empty_eq : Φ ∪ x = x := Class.eq fun _ => Union.elim_empty

theorem Inter.elim_empty : y ∈ Φ ∩ x ↔ y ∈ Φ := Iff.intro
  (fun h => And.left (Inter.split h))
  (fun h => Class.not_in_empty.elim h)
theorem Inter.elim_empty_eq : Φ ∩ x = Φ := Class.eq fun _ => Inter.elim_empty

noncomputable def μ := Classify fun _ => True

theorem Class.in_complete : x ∈ μ ↔ Ensemble x := Iff.intro
  (fun h => And.left (Class.classify.mp h))
  (fun h => Class.classify.mpr ⟨h, trivial⟩)

theorem Union.elim_complete : y ∈ x ∪ μ ↔ y ∈ μ := Iff.intro
  (fun h => Class.in_complete.mpr ⟨x ∪ μ, h⟩)
  (fun h => Union.intro (Or.inr h))
theorem Union.elim_complete_eq : x ∪ μ = μ := Class.eq fun _ => Union.elim_complete

theorem Inter.elim_complete : y ∈ x ∩ μ ↔ y ∈ x := Iff.intro
  (fun h => And.left (Inter.split h))
  (fun h => Inter.intro ⟨h, Class.in_complete.mpr ⟨x, h⟩⟩)
theorem Inter.elim_complete_eq : x ∩ μ = x := Class.eq fun _ => Inter.elim_complete

theorem complete_compl_empty : x ∈ μ ↔ x ∈ ~~~Φ := Iff.intro
  (fun h => Class.classify.mpr ⟨⟨μ, h⟩, Class.not_in_empty⟩)
  (fun h => Class.in_complete.mpr ⟨~~~Φ, h⟩)
theorem complete_compl_empty_eq : μ = ~~~Φ := Class.eq fun _ => complete_compl_empty

theorem empty_compl_complete : x ∈ Φ ↔ x ∈ ~~~μ := Iff.intro
  (fun h => Class.not_in_empty.elim h)
  (fun h => have ⟨ensx, not⟩ := Class.classify.mp h; not.elim (Class.in_complete.mpr ensx))
theorem empty_compl_complete_eq : Φ = ~~~μ := Class.eq fun _ => empty_compl_complete

noncomputable def SInter (x : Class) := Classify fun z => ∀ y, y ∈ x → z ∈ y
noncomputable def SUnion (x : Class) := Classify fun z => ∃ y, z ∈ y ∧ y ∈ x

prefix:85 "∩" => SInter
prefix:85 "∪" => SUnion

theorem sinter_empty_is_complete : x ∈ ∩Φ ↔ x ∈ μ := Iff.intro
  (fun h => Class.in_complete.mpr ⟨∩Φ, h⟩)
  (fun h => Class.classify.mpr ⟨⟨μ, h⟩, fun _ fake => Class.not_in_empty.elim fake⟩)
theorem sinter_empty_is_complete_eq : ∩Φ = μ := Class.eq fun _ => sinter_empty_is_complete

theorem sunion_empty_is_empty : x ∈ ∪Φ ↔ x ∈ Φ := Iff.intro
  (fun h => have ⟨_, ⟨_, h1⟩⟩ := Class.classify.mp h; Not.elim Class.not_in_empty h1.right)
  (fun h => Class.not_in_empty.elim h)
theorem sunion_empty_is_empty_eq : ∪Φ = Φ := Class.eq fun _ => sunion_empty_is_empty

instance : HasSubset Class where
  Subset x y := ∀ z, z ∈ x → z ∈ y

theorem apply_subset : x ⊆ y → z ∈ x → z ∈ y := fun h h1 => h z h1

theorem empty_is_subset : Φ ⊆ x := fun _ h => Class.not_in_empty.elim h
theorem complete_is_superset : x ⊆ μ := fun _ h => Class.in_complete.mpr ⟨x, h⟩
@[refl] theorem subset_rfl : x ⊆ x := fun _ => id 

@[symm] theorem subset_antisymm : x ⊆ y ∧ y ⊆ x ↔ x = y := Iff.intro
  (fun ⟨h1, h2⟩ => Class.eq fun z => Iff.intro (fun zsx => h1 z zsx) (fun zsy => h2 z zsy))
  (fun h => by rw[h]; exact ⟨subset_rfl, subset_rfl⟩)

theorem subset_with_union : x ⊆ y → x ⊆ y ∪ z := fun h w wsx => Union.intro (Or.inl (h w wsx))
theorem subset_of_union : x ⊆ x ∪ y := subset_with_union subset_rfl
theorem subset_of_union' : y ⊆ x ∪ y := by rw[Union.comm_eq]; exact subset_of_union
theorem inter_is_subset : x ∩ y ⊆ x := fun _ h => And.left (Inter.split h)

theorem subset_trans : x ⊆ y → y ⊆ z → x ⊆ z := fun h1 h2 w zsx => h2 w (h1 w zsx)

theorem union_absorb_subset : x ∪ y = y ↔ x ⊆ y := Iff.intro
  (fun h => by rw[← h]; exact subset_of_union)
  (fun h => Class.eq fun z => Iff.intro
    (fun zsxy => (Union.split zsxy).elim (fun zsx => h z zsx) id)
    (fun zsy => Union.intro (Or.inr zsy)))
theorem inter_absorb_subset : x ∩ y = x ↔ x ⊆ y := Iff.intro
  (fun h => by rw[← h]; rw[Inter.comm_eq]; exact inter_is_subset)
  (fun h => Class.eq fun z => Iff.intro
    (fun zsxy => And.left (Inter.split zsxy))
    (fun zsx => Inter.intro ⟨zsx, h z zsx⟩))

theorem sunion_monotone : x ⊆ y → ∪x ⊆ ∪y := fun h _ zsux =>
  have ⟨ensz, ⟨w, ⟨zsw, wsx⟩⟩⟩ := Class.classify.mp zsux
  Class.classify.mpr ⟨ensz, ⟨w, ⟨zsw, h w wsx⟩⟩⟩
theorem sinter_monotone : x ⊆ y → ∩y ⊆ ∩x := fun h _ zsiy =>
  have ⟨ensz, h1⟩ := Class.classify.mp zsiy
  Class.classify.mpr ⟨ensz, fun w wsx => have wsy := h w wsx; h1 w wsy⟩

theorem sunion_monotone_mem : x ∈ y → x ⊆ ∪y := fun xsy _ zsx  =>
  Class.classify.mpr ⟨⟨x, zsx⟩, ⟨x, ⟨zsx, xsy⟩⟩⟩
theorem sinter_monotone_mem : x ∈ y → ∩y ⊆ x := fun xsy _ zsiy =>
  And.right (Class.classify.mp zsiy) x xsy

axiom Class.subsets : ∀ {x}, Ensemble x → ∃ y, Ensemble y ∧ (∀ z, z ⊆ x -> z ∈ y)

theorem Ensemble.recursive : Ensemble x → ∃ y, Ensemble y ∧ x ∈ y := fun h =>
  have ⟨y, ⟨ensy, h1⟩⟩ := (Class.subsets h)
  ⟨y, ⟨ensy, h1 x subset_rfl⟩⟩

theorem Ensemble.mp : Ensemble x → y ⊆ x → Ensemble y := fun ensx h =>
  have ⟨z, ⟨_, h1⟩⟩ := Class.subsets ensx
  ⟨z, h1 y h⟩

theorem sinter_complete_is_empty : x ∈ ∩μ ↔ x ∈ Φ := Iff.intro
  (fun h =>
    have ⟨ensx, h1⟩ := Class.classify.mp h
    have h2 := Ensemble.mp ensx empty_is_subset
    h1 Φ (Class.in_complete.mpr h2))
  (fun h =>(Class.not_in_empty h).elim)
theorem sinter_complete_is_empty_eq : ∩μ = Φ := Class.eq fun _ => sinter_complete_is_empty

theorem sunion_complete_is_complete : x ∈ ∪μ ↔ x ∈ μ := Iff.intro
  (fun h =>
    have ⟨_, ⟨y, xsy, _⟩⟩ := Class.classify.mp h
    Class.in_complete.mpr ⟨y, xsy⟩)
  (fun h =>
    have ensx := Class.in_complete.mp h
    have ⟨y, ⟨ensy, xsy⟩⟩ := Ensemble.recursive ensx
    Class.classify.mpr ⟨ensx, ⟨y, ⟨xsy, Class.in_complete.mpr ensy⟩⟩⟩)
theorem sunion_complete_is_complete_eq : ∪μ = μ := Class.eq fun _ => sunion_complete_is_complete

theorem sib_exist_non_empty : x ≠ Φ ↔ ∃ y, y ∈ x := Iff.intro
  (fun h => Classical.byContradiction fun fake =>
    h (Class.eq fun z => Iff.intro
      (fun h1 => (not_exists.mp fake z h1).elim)
      (fun h1 => (Class.not_in_empty h1).elim)) )
  (fun ⟨y, ysx⟩ => Not.intro fun fake =>
    have fake1 : y ∈ Φ := by rw[fake] at ysx; exact ysx
    Class.not_in_empty fake1)

theorem sinter_ens_non_empty : x ≠ Φ → Ensemble (∩x) := fun h =>
  have ⟨_, ysx⟩ := sib_exist_non_empty.mp h
  Ensemble.mp (Ensemble.intro ysx) (sinter_monotone_mem ysx)

noncomputable def Power (x : Class) := Classify fun y => y ⊆ x
noncomputable def pow := Power

theorem complete_power_rfl : x ∈ μ ↔ x ∈ pow μ := Iff.intro
  (fun h => Class.classify.mpr ⟨Class.in_complete.mp h, complete_is_superset⟩)
  (fun h => have ⟨ensx, _⟩ := Class.classify.mp h; Class.in_complete.mpr ensx)
theorem complete_power_rfl_eq : μ = pow μ := Class.eq fun _ => complete_power_rfl

theorem Ensemble.map_pow : Ensemble x → Ensemble (pow x) := fun ensx =>
  have ⟨_, ⟨ensy, h⟩⟩ := Class.subsets ensx
  Ensemble.mp ensy fun z zpx => have ⟨_, zssx⟩ := Class.classify.mp zpx; h z zssx

theorem Class.subsets_pow : Ensemble x → ∀ y, y ⊆ x ↔ y ∈ pow x := fun ensx _ => Iff.intro
  (fun h => Class.classify.mpr ⟨Ensemble.mp ensx h, h⟩)
  (fun h => have ans := And.right (Class.classify.mp h); ans)

theorem Class.in_pow : Ensemble x → x ∈ pow x := fun h =>
  Class.classify.mpr ⟨h, subset_rfl⟩

noncomputable def Nens := Classify fun x => x ∉ x

theorem Nens.nens : ¬Ensemble Nens := fun ensn => Classical.byCases
  (fun h : Nens ∈ Nens => have ⟨_, h1⟩ := Class.classify.mp h; h1 h)
  (fun h : Nens ∉ Nens => h (Class.classify.mpr ⟨ensn, h⟩))

theorem complete_nens : ¬Ensemble μ := fun ensm =>
  Nens.nens (Ensemble.mp ensm complete_is_superset)

noncomputable instance : Singleton Class Class where
  singleton x := Classify fun y => x ∈ μ → y = x

noncomputable def singleton (x : Class) : Class := {x}

theorem Class.in_singleton : Ensemble x → x ∈ singleton x := fun ensx =>
  Class.classify.mpr ⟨ensx, fun _ => rfl⟩

theorem singleton_eq : Ensemble y → x ∈ ({y} : Class) → x = y := fun ensy h =>
  have ⟨_, h1⟩ := Class.classify.mp h
  h1 (Class.in_complete.mpr ensy)

theorem singleton_eq' : Ensemble x → x = y → x ∈ ({y} : Class) := fun ex h => by
  rw[← h]; exact Class.in_singleton ex

theorem singleton_mp : x ∈ singleton y → y = z → x ∈ singleton z := fun h eq =>
  by rw[← eq]; exact h

theorem singleton_mpr : Ensemble x → y ∈ singleton x ∧ z ∈ singleton x → y = z := fun ensx ⟨h1, h2⟩ =>
  have ⟨ensy, h1⟩ := Class.classify.mp h1
  have ⟨ensz, h2⟩ := Class.classify.mp h2
  by simp[h1, h2, Class.in_complete.mpr ensx]
theorem singleton_smpr : Ensemble x → y ∈ singleton x → x = y := fun ensx h =>
  singleton_mpr ensx ⟨Class.in_singleton ensx, h⟩

theorem singleton_subset_pow : Ensemble x → {x} ⊆ pow x := fun ensx y h =>
  have h1 := singleton_smpr ensx h
  by simp[h1]; rw[← h1]; exact Class.in_pow ensx

theorem Ensemble.map_singleton : Ensemble x → Ensemble {x} := fun ensx =>
  Ensemble.mp (Ensemble.map_pow ensx) (singleton_subset_pow ensx)

theorem nens_singleton_is_complete : {x} = μ ↔ ¬Ensemble x := Iff.intro
  (fun h => complete_nens.imp fun ensx =>
    have h1 := Ensemble.map_singleton ensx
    by rw[h] at h1; exact h1)
  (fun h => Class.eq fun y => Iff.intro
    (fun h1 => complete_is_superset y h1)
    (fun h1 => have ensy := Class.in_complete.mp h1
      Class.classify.mpr ⟨ensy, fun fake => h.elim (Class.in_complete.mp fake)⟩))

theorem Ensemble.unwrap_singleton : Ensemble {x} → Ensemble x := fun h => Classical.byContradiction fun fake =>
  have eq := nens_singleton_is_complete.mpr fake
  by rw[eq] at h; exact complete_nens h 

theorem Ensemble.iff_singleton : Ensemble x ↔ Ensemble {x} := Iff.intro Ensemble.map_singleton Ensemble.unwrap_singleton

theorem sinter_singleton_rfl : Ensemble x → ∩{x} = x := fun h => Class.eq fun y => Iff.intro
  (fun h1 =>
    have ⟨ensy, h2⟩ := Class.classify.mp h1
    h2 x (Class.in_singleton h))
  (fun h1 => Class.classify.mpr ⟨⟨x, h1⟩, fun z h2 =>
    have ⟨ensz, h3⟩ := Class.classify.mp h2
    have h3 := h3 (Class.in_complete.mpr h)
    by rw[← h3] at h1; exact h1⟩)

theorem sunion_singleton_rfl : Ensemble x → ∪{x} = x := fun h => Class.eq fun y => Iff.intro
  (fun h1 =>
    have ⟨ensy, ⟨z, ⟨h2, h3⟩⟩⟩ := Class.classify.mp h1
    have h4 := singleton_smpr h h3
    by rw[← h4] at h2; exact h2)
  (fun h1 => Class.classify.mpr ⟨⟨x, h1⟩, ⟨x, ⟨h1, Class.in_singleton h⟩⟩⟩)

theorem nens_sinter_singleton : ¬Ensemble x → ∩{x} = Φ := fun h =>
  have h1 := nens_singleton_is_complete.mpr h
  by rw[h1]; apply sinter_complete_is_empty_eq

theorem nens_sunion_singleton : ¬Ensemble x → ∪{x} = μ := fun h =>
  have h1 := nens_singleton_is_complete.mpr h
  by rw[h1]; apply sunion_complete_is_complete_eq

axiom Ensemble.map_union : Ensemble x → Ensemble y → Ensemble (x ∪ y)

theorem Ensemble.unwrap_union : Ensemble (x ∪ y) → Ensemble x ∧ Ensemble y := fun h =>
  ⟨Ensemble.mp h subset_of_union, Ensemble.mp h subset_of_union'⟩

-- unordered
noncomputable instance : Insert Class Class where
  insert x y := {x} ∪ y

noncomputable def Unordered (x y : Class) : Class := {x, y}

theorem Ensemble.map_unordered : Ensemble x → Ensemble y → Ensemble {x, y} := fun h1 h2 =>
  Ensemble.map_union (Ensemble.map_singleton h1) (Ensemble.map_singleton h2)
theorem Ensemble.unwrap_unordered : Ensemble {x, y} → Ensemble x ∧ Ensemble y := fun h =>
  (Ensemble.unwrap_union h).imp Ensemble.unwrap_singleton Ensemble.unwrap_singleton

theorem Ensemble.map_unordered_iff : Ensemble x ∧ Ensemble y ↔ Ensemble {x, y} := Iff.intro
  (fun ⟨a, b⟩ => Ensemble.map_unordered a b)
  Ensemble.unwrap_unordered

theorem pick_from_unordered_iff : Ensemble x → Ensemble y → (∀ z, z ∈ ({x, y} : Class) ↔ z = x ∨ z = y) := fun ensx ensy z => Iff.intro
  (fun zsxy => have ⟨ensz, or⟩ := Class.classify.mp zsxy
    have intermediary := or.imp (singleton_smpr ensx) (singleton_smpr ensy)
    intermediary.imp Eq.symm Eq.symm)
  (fun h => h.elim
    (fun h => by rw[h]; exact Union.intro (Or.inl (Class.in_singleton ensx)))
    (fun h => by rw[h]; exact Union.intro (Or.inr (Class.in_singleton ensy))))

theorem pick_from_unordered : Ensemble x → Ensemble y → z ∈ ({x, y} : Class) → z = x ∨ z = y := fun ex ey h =>
  (pick_from_unordered_iff ex ey z).mp h

theorem pick_from_unordered3 : Ensemble a → Ensemble b → Ensemble c → x ∈ ({a, b, c} : Class) → x = a ∨ x = b ∨ x = c :=
  fun ea eb ec h => (Union.split h).imp (singleton_eq ea) (pick_from_unordered eb ec)

theorem in_unordered : Ensemble x → x ∈ ({x, y} : Class) := fun ensx =>
  Union.intro (Or.inl (Class.in_singleton ensx))
theorem in_unordered' : Ensemble y → y ∈ ({x, y} : Class) := fun ensy =>
  Union.intro (Or.inr (Class.in_singleton ensy))

theorem in_unordered3 : Ensemble a → a ∈ ({a, b, c} : Class) := fun e => Union.intro (Or.inl (Class.in_singleton e))
theorem in_unordered3' : Ensemble b → b ∈ ({a, b, c} : Class) := fun e => Union.intro (Or.inr (Union.intro (Or.inl (Class.in_singleton e))))
theorem in_unordered3'' : Ensemble c → c ∈ ({a, b, c} : Class) := fun e => Union.intro (Or.inr (Union.intro (Or.inr (Class.in_singleton e))))

theorem nens_unordered_complete : ¬Ensemble x ∨ ¬Ensemble y ↔ {x, y} = μ := Iff.intro
  (fun h =>
    have h1 := h.imp nens_singleton_is_complete.mpr nens_singleton_is_complete.mpr
    h1.elim
      (fun h2 => by show ({x} ∪ {y} = μ); rw[h2]; rw[Union.comm_eq]; apply Union.elim_complete_eq)
      (fun h2 => by show ({x} ∪ {y} = μ); rw[h2]; apply Union.elim_complete_eq))
  (fun h =>
    have h1 : ¬Ensemble {x, y} := by have h1 := complete_nens; rw[← h] at h1; exact h1
    Classical.not_and_iff_not_or_not.mp (h1.imp Ensemble.map_unordered_iff.mp))

theorem sinter_unordered_is_inter : Ensemble x ∧ Ensemble y → ∩{x, y} = x ∩ y := fun ⟨ensx, ensy⟩ => Class.eq fun z => Iff.intro
  (fun h => have ⟨ensz, h1⟩ := Class.classify.mp h; Inter.intro ⟨h1 x (in_unordered ensx), h1 y (in_unordered' ensy)⟩)
  (fun h =>
    have ⟨h1, h2⟩ := Inter.split h
    Class.classify.mpr ⟨Ensemble.intro h, fun w h =>
      have h3 := (pick_from_unordered_iff ensx ensy w).mp h
      h3.elim (fun h => by rw[h]; exact h1) (fun h => by rw[h]; exact h2)⟩)

theorem sunion_unordered_is_union : Ensemble x ∧ Ensemble y → ∪{x, y} = x ∪ y := fun ⟨ensx, ensy⟩ => Class.eq fun z => Iff.intro
  (fun h =>
    have ⟨ensz, ⟨w, ⟨h1, h2⟩⟩⟩ := Class.classify.mp h
    have h3 := (pick_from_unordered_iff ensx ensy w).mp h2
    Union.intro (h3.imp (fun h => by rw[← h]; exact h1) (fun h => by rw[← h]; exact h1)))
  (fun h =>
    have h1 := Union.split h
    Class.classify.mpr (And.intro (Ensemble.intro h)
    (h1.elim
      (fun h => ⟨x, ⟨h, in_unordered  ensx⟩⟩)
      (fun h => ⟨y, ⟨h, in_unordered' ensy⟩⟩))))

noncomputable def Ordered (x y : Class) : Class := {{x}, {x, y}}

macro_rules
| `(($a , $b)) => `(Ordered $a $b)

theorem Ensemble.map_ordered : Ensemble x → Ensemble y → Ensemble (x, y) := fun ensx ensy =>
  Ensemble.map_unordered (Ensemble.map_singleton ensx) (Ensemble.map_unordered ensx ensy)

theorem Ensemble.unwrap_ordered : Ensemble (x, y) → Ensemble x ∧ Ensemble y := fun h => And.imp
  Ensemble.unwrap_singleton
  (fun h => And.right (Ensemble.unwrap_unordered h))
  (Ensemble.unwrap_unordered h)

theorem Ensemble.unwrap_ordered_l : Ensemble (x, y) → Ensemble x := fun h => And.left (Ensemble.unwrap_ordered h)
theorem Ensemble.unwrap_ordered_r : Ensemble (x, y) → Ensemble y := fun h => And.right (Ensemble.unwrap_ordered h)

theorem Ensemble.swap_ordered : Ensemble (x, y) → Ensemble (y, x) := fun ens =>
  Ensemble.map_ordered (Ensemble.unwrap_ordered_r ens) (Ensemble.unwrap_ordered_l ens)

theorem Ensemble.map_ordered_iff : Ensemble x ∧ Ensemble y ↔ Ensemble (x, y) := Iff.intro
  (fun ⟨h1, h2⟩ => Ensemble.map_ordered h1 h2) Ensemble.unwrap_ordered

theorem nens_ordered_complete : ¬Ensemble x ∨ ¬Ensemble y ↔ (x, y) = μ := Iff.intro
  (fun h => by
      have h1 := nens_unordered_complete.mp h
      show {{x}, {x, y}} = μ; rw[h1]
      exact nens_unordered_complete.mp (Or.inr complete_nens))
  (fun h => Or.elim (nens_unordered_complete.mpr h)
    (fun h => Or.inl (h.imp Ensemble.map_singleton))
    (fun h => Classical.not_and_iff_not_or_not.mp (h.imp Ensemble.map_unordered_iff.mp)))

theorem sunion_ordered_is_unordered : Ensemble x ∧ Ensemble y → ∪(x, y) = {x, y} := fun ⟨ensx, ensy⟩ => Class.eq fun z =>
  have h1 := sunion_unordered_is_union ⟨Ensemble.map_singleton ensx, Ensemble.map_unordered ensx ensy⟩
  Iff.intro
    (fun h =>
      have h2 := Union.split ((Class.eq_iff.mp h1 z).mp h)
      h2.elim (fun h => Union.intro (Or.inl h)) id)
    (fun h => by
      show z ∈ ∪{{x}, {x, y}}; rw[h1]
      exact Union.intro (Or.inr h))

theorem sinter_ordered_is_singleton : Ensemble x ∧ Ensemble y → ∩(x, y) = {x} := fun ⟨ensx, ensy⟩ => Class.eq fun z =>
  have h1 := sinter_unordered_is_inter ⟨Ensemble.map_singleton ensx, Ensemble.map_unordered ensx ensy⟩
  by
    show z ∈ ∩{{x}, {x, y}} ↔ z ∈ {x}; rw[h1];
    exact Iff.intro
      (fun h => And.left (Inter.split h))
      (fun h => Inter.intro ⟨h, Union.intro (Or.inl h)⟩)

-- unwraps an Ordered
noncomputable def First x := ∩∩x
noncomputable def Second x := (∩∪x) ∪ (∪∪x - ∪∩x)

theorem second_complete_is_complete : Second μ = μ := by
  show ∩∪μ ∪ (∪∪μ - ∪∩μ) = μ
  rw[sunion_complete_is_complete_eq, sinter_complete_is_empty_eq, sunion_empty_is_empty_eq, sunion_complete_is_complete_eq]
  rw[Union.elim_empty_eq]; exact Sub.elim_empty_eq

theorem unwrap_ordered_first : Ensemble x ∧ Ensemble y → First (x, y) = x := fun h => by
  show ∩∩(x, y) = x
  rw[sinter_ordered_is_singleton h, sinter_singleton_rfl]
  exact h.left

theorem unwrap_ordered_second : Ensemble x ∧ Ensemble y → Second (x, y) = y := fun h => by
  show ∩∪(x, y) ∪ (∪∪(x, y) - ∪∩(x, y)) = y
  rw[sunion_ordered_is_unordered h, sinter_ordered_is_singleton h, sinter_unordered_is_inter h, sunion_unordered_is_union h]
  rw[sunion_singleton_rfl h.left]
  exact Class.eq fun z => Iff.intro
    (fun h => (Union.split h).elim (fun h => And.right (Inter.split h)) Sub.elim_union)
    (fun h => Union.intro (Classical.byCases
      (fun h1 : z ∈ x => Or.inl (Inter.intro ⟨h1, h⟩))
      (fun h1 : z ∉ x => Or.inr (Sub.intro (Union.intro (Or.inr h)) h1))))

theorem nens_ordered_components_complete : ¬Ensemble x ∨ ¬Ensemble y → First (x, y) = μ ∧ Second (x, y) = μ := fun h => by
  show ∩∩(x, y) = μ ∧ (∩∪(x, y)) ∪ (∪∪(x, y) - ∪∩(x, y)) = μ
  rw[nens_ordered_complete.mp h]
  rw[sinter_complete_is_empty_eq, sunion_complete_is_complete_eq, sinter_empty_is_complete_eq]
  rw[sinter_complete_is_empty_eq, sunion_complete_is_complete_eq, sunion_empty_is_empty_eq]
  rw[Sub.elim_empty_eq, Union.elim_empty_eq]
  constructor
  · rfl
  · rfl

theorem ordered_rfl : Ensemble x ∧ Ensemble y → ((x, y) = (u, v) ↔ x = u ∧ y = v) := fun ens => Iff.intro
  (fun h =>
    have snd := unwrap_ordered_second ens
    have ens' := Ensemble.unwrap_ordered (by have enso := Ensemble.map_ordered ens.left ens.right; rw[h] at enso; exact enso)
    have hx : x = u := by
      have fst := unwrap_ordered_first ens;
      have fst' := unwrap_ordered_first ens'
      rw[h] at fst; exact Eq.trans fst.symm fst'
    have hy : y = v := by
      have snd := unwrap_ordered_second ens;
      have snd' := unwrap_ordered_second ens'
      rw[h] at snd; exact Eq.trans snd.symm snd'
    ⟨hx, hy⟩)
  fun ⟨h1, h2⟩ => by rw[h1, h2]

theorem singleton_ordered_rfl : Ensemble u → Ensemble v → (x, y) ∈ ({(u, v)} : Class) → x = u ∧ y = v := fun eu ev h =>
  have ens := Ensemble.intro h; ((ordered_rfl (Ensemble.unwrap_ordered ens)).mp (singleton_eq (Ensemble.map_ordered eu ev) h))
theorem singleton_ordered_rflr : Ensemble x → Ensemble y → x = u ∧ y = v → (x, y) ∈ ({(u, v)} : Class) := fun ensx ensy ⟨ex, ey⟩ => by
  rw[ex.symm, ey.symm]; exact Class.in_singleton (Ensemble.map_ordered ensx ensy)

def Relation (r : Class) := ∀ z, z ∈ r → ∃ x y, z = (x, y)

noncomputable def PairedClassify : (Class → Class → Prop) → Class := fun p =>
  Classify fun z => ∃ x y, z = (x, y) ∧ p x y

theorem PairedClassify.relative {P : Class → Class → Prop} : Relation (PairedClassify P) := fun _ h =>
  have ⟨_, ⟨x, ⟨y, ⟨h1, _⟩⟩⟩⟩ := Class.classify.mp h; ⟨x, ⟨y, h1⟩⟩

theorem Relation.map_union : Relation x → Relation y → Relation (x ∪ y) := fun rx ry z h =>
  (Union.split h).elim (fun h => rx z h) (fun h => ry z h)
theorem Relation.map_inter : Relation x → Relation (x ∩ y) := fun r z h => r z (And.left (Inter.split h))
theorem Relation.map_inter' : Relation y → Relation (x ∩ y) := fun r z h => r z (And.right (Inter.split h))

theorem singleton_relative : Ensemble a → Ensemble b → Relation {(a, b)} := fun ensa ensb _ h =>
  ⟨a, ⟨b, singleton_eq (Ensemble.map_ordered ensa ensb) h⟩⟩

theorem Class.paired_classify {P : Class → Class → Prop} : (x, y) ∈ PairedClassify P ↔ Ensemble (x, y) ∧ P x y := Iff.intro
  (fun h =>
    have ⟨ens, ⟨a, ⟨b, ⟨h1, h2⟩⟩⟩⟩ := Class.classify.mp h
    have ⟨xsa, ysb⟩ := (ordered_rfl (Ensemble.unwrap_ordered ens)).mp h1
    ⟨ens, by rw[← xsa, ← ysb] at h2; exact h2⟩)
  (fun ⟨ens, h⟩ => Class.classify.mpr ⟨ens, ⟨x, ⟨y, ⟨by rfl, h⟩⟩⟩⟩)

theorem Class.paired_eq {a b : Class} : Relation a → Relation b → (∀ x y, (x, y) ∈ a ↔ (x, y) ∈ b) → a = b :=
  fun ra rb h => Class.eq fun z => Iff.intro
    (fun h1 => by have ⟨x, ⟨y, h2⟩⟩ := ra z h1; rw[h2]; rw[h2] at h1; exact (h x y).mp h1)
    (fun h1 => by have ⟨x, ⟨y, h2⟩⟩ := rb z h1; rw[h2]; rw[h2] at h1; exact (h x y).mpr h1)

theorem subset_paired_intro : Relation x → (∀ u v, (u, v) ∈ x → (u, v) ∈ y) → x ⊆ y := fun rx f z h => by
  have ⟨u, v, eq1⟩ := rx z h; rw[eq1] at h; rw[eq1]; exact f u v h

noncomputable def Composition (r s : Class) := PairedClassify fun x z => ∃ y, (x, y) ∈ s ∧ (y, z) ∈ r

infixr:90 " ∘ "  => Composition

variable {a b r s t : Class}

theorem Composition.assoc : (x, y) ∈ (r ∘ s) ∘ t → (x, y) ∈ r ∘ (s ∘ t) := fun h =>
  have ⟨ensxy, ⟨z, ⟨h1, h'⟩⟩⟩ := Class.paired_classify.mp h
  have ⟨_, ⟨w, ⟨h2, h3⟩⟩⟩ := Class.paired_classify.mp h'
  have ensw := Ensemble.unwrap_ordered_r (Ensemble.intro h2)
  have h4 : (x, w) ∈ s ∘ t := Class.paired_classify.mpr ⟨Ensemble.map_ordered (Ensemble.unwrap_ordered_l ensxy) ensw, ⟨z, ⟨h1, h2⟩⟩⟩
  Class.paired_classify.mpr ⟨ensxy, ⟨w, ⟨h4, h3⟩⟩⟩

theorem Composition.assoc' : (x, y) ∈ r ∘ (s ∘ t) → (x, y) ∈ (r ∘ s) ∘ t := fun h =>
  have ⟨ensxy, ⟨z, ⟨h', h1⟩⟩⟩ := Class.paired_classify.mp h
  have ⟨_, ⟨w, ⟨h2, h3⟩⟩⟩ := Class.paired_classify.mp h'
  have ensw := Ensemble.unwrap_ordered_r (Ensemble.intro h2)
  have h4 : (w, y) ∈ r ∘ s := Class.paired_classify.mpr ⟨Ensemble.map_ordered ensw (Ensemble.unwrap_ordered_r ensxy), ⟨z, ⟨h3, h1⟩⟩⟩
  Class.paired_classify.mpr ⟨ensxy, ⟨w, ⟨h2, h4⟩⟩⟩

theorem Composition.assoc_eq : (r ∘ s) ∘ t = r ∘ (s ∘ t) :=
  Class.paired_eq PairedClassify.relative PairedClassify.relative fun _ _ => Iff.intro Composition.assoc Composition.assoc'

theorem Composition.split_union : (x, y) ∈ r ∘ (s ∪ t) → (x, y) ∈ (r ∘ s) ∪ (r ∘ t) := fun h =>
  have ⟨ensxy, ⟨z, ⟨h1, h2⟩⟩⟩ := Class.paired_classify.mp h
  Union.intro ((Union.split h1).imp
    (fun h => Class.paired_classify.mpr ⟨ensxy, ⟨z, ⟨h, h2⟩⟩⟩)
    (fun h => Class.paired_classify.mpr ⟨ensxy, ⟨z, ⟨h, h2⟩⟩⟩))

theorem Composition.merge_union : (x, y) ∈ (r ∘ s) ∪ (r ∘ t) → (x, y) ∈ r ∘ (s ∪ t) := fun h => (Union.split h).elim
  (fun h =>
    have ⟨ensxy, ⟨z, ⟨h1, h2⟩⟩⟩ := Class.paired_classify.mp h
    Class.paired_classify.mpr ⟨ensxy, ⟨z, ⟨Union.intro (Or.inl h1), h2⟩⟩⟩)
  (fun h =>
    have ⟨ensxy, ⟨z, ⟨h1, h2⟩⟩⟩ := Class.paired_classify.mp h
    Class.paired_classify.mpr ⟨ensxy, ⟨z, ⟨Union.intro (Or.inr h1), h2⟩⟩⟩)

theorem Composition.dist_union_eq : r ∘ (s ∪ t) = (r ∘ s) ∪ (r ∘ t) := Class.paired_eq
  PairedClassify.relative (Relation.map_union PairedClassify.relative PairedClassify.relative)
  fun _ _ => Iff.intro Composition.split_union Composition.merge_union

theorem Composition.dist_inter_ss : r ∘ (s ∩ t) ⊆ (r ∘ s) ∩ (r ∘ t) := fun z h => by
  have ⟨x, ⟨y, eq⟩⟩ := PairedClassify.relative z h; rw[eq]; rw[eq] at h;
  have ⟨ensxy, ⟨z, ⟨h', h2⟩⟩⟩ := Class.paired_classify.mp h; have ⟨h3, h4⟩ := Inter.split h'
  exact Inter.intro ⟨Class.paired_classify.mpr ⟨ensxy, ⟨z, ⟨h3, h2⟩⟩⟩, Class.paired_classify.mpr ⟨ensxy, ⟨z, ⟨h4, h2⟩⟩⟩⟩

noncomputable instance : Inv Class where
  inv r := PairedClassify fun x y => (y, x) ∈ r

variable {f g : Class}

theorem inv_iff : (a, b) ∈ f ↔ (b, a) ∈ f⁻¹ := Iff.intro
  (fun h => Class.paired_classify.mpr ⟨Ensemble.swap_ordered (Ensemble.intro h), h⟩)
  (fun h => have ⟨_, h1⟩ := Class.paired_classify.mp h; h1)

theorem inv_map_union : (x, y) ∈ a⁻¹ ∪ b⁻¹ → (x, y) ∈ (a ∪ b)⁻¹ := fun h =>
  Class.paired_classify.mpr ⟨Ensemble.intro h, Union.intro ((Union.split h).imp inv_iff.mpr inv_iff.mpr)⟩

theorem inv_unwrap_union : (x, y) ∈ (a ∪ b)⁻¹ → (x, y) ∈ a⁻¹ ∪ b⁻¹ := fun h =>
  have ⟨_, h1⟩ := Class.paired_classify.mp h
  Union.intro ((Union.split h1).imp inv_iff.mp inv_iff.mp)

theorem inv_dist_union_eq : a⁻¹ ∪ b⁻¹ = (a ∪ b)⁻¹ := Class.paired_eq
  (Relation.map_union PairedClassify.relative PairedClassify.relative) PairedClassify.relative
  fun _ _ => Iff.intro inv_map_union inv_unwrap_union

theorem inv_map_inter : (x, y) ∈ a⁻¹ ∩ b⁻¹ → (x, y) ∈ (a ∩ b)⁻¹ := fun h =>
  have h1 := Inter.split h
  Class.paired_classify.mpr ⟨Ensemble.intro h, Inter.intro (h1.imp inv_iff.mpr inv_iff.mpr)⟩

theorem inv_unwrap_inter : (x, y) ∈ (a ∩ b)⁻¹ → (x, y) ∈ a⁻¹ ∩ b⁻¹ := fun h =>
  have ⟨_, h1⟩ := Class.paired_classify.mp h;
  Inter.intro ((Inter.split h1).imp inv_iff.mp inv_iff.mp)

theorem inv_dist_inter_eq : a⁻¹ ∩ b⁻¹ = (a ∩ b)⁻¹ := Class.paired_eq
  (Relation.map_inter PairedClassify.relative) PairedClassify.relative
  fun _ _ => Iff.intro inv_map_inter inv_unwrap_inter

theorem inv_in_singleton : Ensemble a → Ensemble b → {(a, b)}⁻¹ = ({(b, a)} : Class) := fun ensa ensb => Class.paired_eq
  PairedClassify.relative (singleton_relative ensb ensa)
  fun x y => Iff.intro
    (fun h => by
      have ⟨ens, h1⟩ := Class.paired_classify.mp h
      have ⟨eq0, eq1⟩ := (ordered_rfl (Ensemble.unwrap_ordered ens).symm).mp (singleton_eq (Ensemble.map_ordered ensa ensb) h1)
      rw[eq0, eq1]; exact Class.in_singleton (Ensemble.map_ordered ensb ensa))
    (fun h => by
      have h1 := singleton_eq (Ensemble.map_ordered ensb ensa) h
      have ⟨eq0, eq1⟩ := (ordered_rfl ⟨ensb, ensa⟩).mp h1.symm
      rw[eq0.symm, eq1.symm]; exact inv_iff.mp (Class.in_singleton (Ensemble.map_ordered ensa ensb)))

theorem inv_elim_eq : Relation r → r⁻¹⁻¹ = r := fun rel => Class.paired_eq
  PairedClassify.relative rel
  fun x y => Iff.intro
    (fun h => have ⟨_, h'⟩ := Class.paired_classify.mp h; have ⟨_, h1⟩ := Class.paired_classify.mp h'; h1)
    (fun h => have ens := Ensemble.intro h;
      have h1 : (y, x) ∈ r⁻¹ := Class.paired_classify.mpr ⟨ens.swap_ordered, h⟩
      Class.paired_classify.mpr ⟨ens, h1⟩)

theorem inv_elim: Relation r → (x, y) ∈ r⁻¹⁻¹ → (x, y) ∈ r := fun rel h => by rw[inv_elim_eq rel] at h; exact h

theorem inv_map_composition : (x, y) ∈ s⁻¹ ∘ r⁻¹ → (x, y) ∈ (r ∘ s)⁻¹ := fun h =>
  have ⟨ens, ⟨z, ⟨h1, h2⟩⟩⟩ := Class.paired_classify.mp h
  have ⟨_, h3⟩ := Class.paired_classify.mp h1; have ⟨_, h4⟩ := Class.paired_classify.mp h2
  Class.paired_classify.mpr ⟨ens, Class.paired_classify.mpr ⟨ens.swap_ordered, ⟨z, ⟨h4, h3⟩⟩⟩⟩

theorem inv_unwrap_composition : (x, y) ∈ (r ∘ s)⁻¹ → (x, y) ∈ s⁻¹ ∘ r⁻¹ := fun h =>
  have ⟨ens, h1⟩ := Class.paired_classify.mp h
  have ⟨_, ⟨z, h2⟩⟩ := Class.paired_classify.mp h1
  Class.paired_classify.mpr ⟨ens, ⟨z, h2.symm.imp inv_iff.mp inv_iff.mp⟩⟩

theorem inv_composition_eq : s⁻¹ ∘ r⁻¹ = (r ∘ s)⁻¹ := Class.paired_eq
  PairedClassify.relative PairedClassify.relative
  fun _ _ => Iff.intro inv_map_composition inv_unwrap_composition

def Function f := Relation f ∧ (∀ x y z, (x, y) ∈ f → (x, z) ∈ f → y = z)

theorem Function.yeq : Function f → (x, y) ∈ f → (x, z) ∈ f → y = z := fun ff h1 h2 =>
  ff.right x y z h1 h2
theorem Function.inv_xeq : Function f⁻¹ → (x, y) ∈ f → (z, y) ∈ f → x = z := fun ff h1 h2 =>
  ff.right y x z (inv_iff.mp h1) (inv_iff.mp h2)

theorem singleton_functional : Ensemble a → Ensemble b → Function {(a, b)} := fun ensa ensb =>
  ⟨singleton_relative ensa ensb, fun _ _ _ l r =>
    have ⟨_, h2⟩ := (ordered_rfl ⟨ensa, ensb⟩).mp (singleton_eq (Ensemble.map_ordered ensa ensb) l).symm
    have ⟨_, h3⟩ := (ordered_rfl ⟨ensa, ensb⟩).mp (singleton_eq (Ensemble.map_ordered ensa ensb) r).symm
    Eq.trans h2.symm h3⟩

theorem Function.map_composition : Function f → Function g → Function (f ∘ g) := fun ff fg =>
  ⟨PairedClassify.relative, fun x y z l r => by
    have ⟨ens, ⟨a, ⟨h1, h2⟩⟩⟩ := Class.paired_classify.mp l
    have ⟨_, ⟨b, ⟨h3, h4⟩⟩⟩ := Class.paired_classify.mp r
    have e := fg.right x a b h1 h3; rw[← e] at h4; 
    exact ff.right a y z h2 h4⟩

noncomputable def Domain (f : Class) := Classify fun x => ∃ y, (x, y) ∈ f
noncomputable def dom := Domain
theorem Domain.intro : (x, y) ∈ f → x ∈ dom f := fun h =>
  Class.classify.mpr ⟨(Ensemble.intro h).unwrap_ordered_l, ⟨y, h⟩⟩

noncomputable def Range (f : Class) := Classify fun y => ∃ x, (x, y) ∈ f
noncomputable def ran := Range
theorem Range.intro : (x, y) ∈ f → y ∈ ran f := fun h =>
  Class.classify.mpr ⟨(Ensemble.intro h).unwrap_ordered_r, ⟨x, h⟩⟩

theorem inv_ran_is_dom : x ∈ ran f⁻¹ → x ∈ dom f := fun h =>
  have ⟨_, ⟨_, h1⟩⟩ := Class.classify.mp h; Domain.intro (inv_iff.mpr h1)
theorem inv_dom_is_ran : x ∈ dom f⁻¹ → x ∈ ran f := fun h =>
  have ⟨_, ⟨_, h1⟩⟩ := Class.classify.mp h; Range.intro (inv_iff.mpr h1)
theorem ran_is_inv_dom : x ∈ ran f → x ∈ dom f⁻¹ := fun h =>
  have ⟨_, ⟨y, h1⟩⟩ := Class.classify.mp h; Class.classify.mpr ⟨Ensemble.intro h, ⟨y, inv_iff.mp h1⟩⟩
theorem dom_is_inv_ran : x ∈ dom f → x ∈ ran f⁻¹ := fun h =>
  have ⟨_, ⟨y, h1⟩⟩ := Class.classify.mp h; Class.classify.mpr ⟨Ensemble.intro h, ⟨y, inv_iff.mp h1⟩⟩

theorem dom_inv_ran_eq : dom f = ran f⁻¹ := Class.eq fun _ => (Iff.intro dom_is_inv_ran inv_ran_is_dom)
theorem ran_inv_dom_eq : ran f = dom f⁻¹ := Class.eq fun _ => (Iff.intro ran_is_inv_dom inv_dom_is_ran)

theorem subdomain : x ⊆ y → dom x ⊆ dom y := fun h1 z h2 =>
  have ⟨_, ⟨w, h3⟩⟩ := Class.classify.mp h2; Domain.intro (h1 (z, w) h3)

theorem Domain.map_union : x ∈ dom f ∪ dom g → x ∈ dom (f ∪ g) := fun h =>
  Class.classify.mpr ⟨Ensemble.intro h, (Union.split h).elim
    (fun h => have ⟨_, ⟨y, h1⟩⟩ := Class.classify.mp h; ⟨y, Union.intro (Or.inl h1)⟩)
    (fun h => have ⟨_, ⟨y, h1⟩⟩ := Class.classify.mp h; ⟨y, Union.intro (Or.inr h1)⟩)⟩
theorem Domain.unwrap_union : x ∈ dom (f ∪ g) → x ∈ dom f ∪ dom g := fun h =>
  have ⟨_, ⟨_, h1⟩⟩ := Class.classify.mp h; (Union.intro ((Union.split h1).imp Domain.intro Domain.intro))
theorem Domain.dist_union_eq : dom f ∪ dom g = dom (f ∪ g) := Class.eq fun _ => (Iff.intro Domain.map_union Domain.unwrap_union)

theorem Range.map_union : x ∈ ran f ∪ ran g → x ∈ ran (f ∪ g) := fun h =>
  Class.classify.mpr ⟨Ensemble.intro h, (Union.split h).elim
    (fun h => have ⟨_, ⟨y, h1⟩⟩ := Class.classify.mp h; ⟨y, Union.intro (Or.inl h1)⟩)
    (fun h => have ⟨_, ⟨y, h1⟩⟩ := Class.classify.mp h; ⟨y, Union.intro (Or.inr h1)⟩)⟩
theorem Range.unwrap_union : x ∈ ran (f ∪ g) → x ∈ ran f ∪ ran g := fun h =>
  have ⟨_, ⟨_, h1⟩⟩ := Class.classify.mp h; (Union.intro ((Union.split h1).imp Range.intro Range.intro))
theorem Range.dist_union_eq : ran f ∪ ran g = ran (f ∪ g) := Class.eq fun _ => (Iff.intro Range.map_union Range.unwrap_union)

theorem singleton_fn_dom_rfl : Ensemble u → Ensemble v → dom {(u, v)} = {u} := fun eu ev => Class.eq fun x => (Iff.intro
    (fun h => by
      have ⟨_, ⟨y, h1⟩⟩ := Class.classify.mp h
      have ⟨h2, _⟩ := singleton_ordered_rfl eu ev h1; rw[h2]
      exact Class.in_singleton eu)
    (fun h => by
      have h1 := singleton_eq eu h; rw[h1]
      exact Domain.intro (Class.in_singleton (Ensemble.map_ordered eu ev)))) 

theorem singleton_fn_ran_rfl : Ensemble u → Ensemble v → ran {(u, v)} = {v} := fun eu ev => Class.eq fun x => (Iff.intro
    (fun h => by
      have ⟨_, ⟨y, h1⟩⟩ := Class.classify.mp h
      have ⟨_, h2⟩ := singleton_ordered_rfl eu ev h1; rw[h2]
      exact Class.in_singleton ev)
    (fun h => by
      have h1 := singleton_eq ev h; rw[h1]
      exact Range.intro (Class.in_singleton (Ensemble.map_ordered eu ev)))) 

theorem Function.include_singular : Function f → Ensemble x → Ensemble y → x ∉ dom f → Function (f ∪ {(x, y)}) := fun ff ex ey h =>
  ⟨Relation.map_union ff.left (singleton_relative ex ey), fun a b c h1 h2 =>
    match (Union.split h1), (Union.split h2) with
    | (Or.inl h1), (Or.inl h2) => ff.right a b c h1 h2
    | (Or.inr h1), (Or.inr h2) =>
      have ⟨_, h3⟩ := singleton_ordered_rfl ex ey h1; have ⟨_, h4⟩ := singleton_ordered_rfl ex ey h2; h3.trans h4.symm
    | (Or.inl h1), (Or.inr h2) => by have ⟨h3, _⟩ := singleton_ordered_rfl ex ey h2; rw[h3] at h1; exact h.elim (Domain.intro h1)
    | (Or.inr h1), (Or.inl h2) => by have ⟨h3, _⟩ := singleton_ordered_rfl ex ey h1; rw[h3] at h2; exact h.elim (Domain.intro h2)⟩

theorem Domain.exclude_singular : Function f → (x, y) ∈ f → (z ∈ dom (f - {(x, y)}) ↔ z ∈ dom f - {x}) := fun ff h1 => Iff.intro
  (fun h2 =>
    have ⟨_, ⟨u, h2'⟩⟩ := Class.classify.mp h2
    have ⟨h3, h4⟩ := Sub.split h2'
    Sub.intro (Domain.intro h3) (h4.imp fun h => by
      have seq := singleton_eq (Ensemble.intro h1).unwrap_ordered_l h 
      rw[seq] at h3; rw[seq]; rw[Function.yeq ff h1 h3]; exact Class.in_singleton (Ensemble.intro h3)))
  (fun h2 =>
    have ⟨h2', h4⟩ := Sub.split h2
    have ⟨_, ⟨u, h3⟩⟩ := Class.classify.mp h2'
    Domain.intro (Sub.intro h3 (h4.imp fun h => by
      have ⟨ex, ey⟩ := Ensemble.unwrap_ordered (Ensemble.intro h1)
      have ⟨eq, _⟩ := singleton_ordered_rfl ex ey h; rw[eq]
      exact Class.in_singleton ex)))
theorem Domain.exclude_singular_eq : Function f → (x, y) ∈ f → dom (f - {(x, y)}) = dom f - {x} :=
  fun ff h1 => Class.eq fun _ => Domain.exclude_singular ff h1

theorem Range.inv_exclude_singular: Function f⁻¹ → (x, y) ∈ f → (z ∈ ran (f - {(x, y)}) ↔ z ∈ ran f - {y}) := fun ff h1 => Iff.intro
  (fun h2 =>
    have ⟨ez, ⟨u, h2'⟩⟩ := Class.classify.mp h2
    have ⟨h3, h4⟩ := Sub.split h2'
    Sub.intro (Range.intro h3) (h4.imp fun h => by
      have seq := singleton_eq (Ensemble.intro h1).unwrap_ordered_r h 
      rw[seq] at h3; rw[seq]; rw[Function.inv_xeq ff h1 h3]; exact Class.in_singleton (Ensemble.intro h3)))
  (fun h2 =>
    have ⟨h2', h4⟩ := Sub.split h2
    have ⟨_, ⟨u, h3⟩⟩ := Class.classify.mp h2'
    Range.intro (Sub.intro h3 (h4.imp fun h => by
      have ⟨ex, ey⟩ := Ensemble.unwrap_ordered (Ensemble.intro h1)
      have ⟨_, eq⟩ := singleton_ordered_rfl ex ey h; rw[eq]
      exact Class.in_singleton ey)))
theorem Range.inv_exclude_singular_eq : Function f⁻¹ → (x, y) ∈ f → ran (f - {(x, y)}) = ran f - {y} :=
  fun ff h1 => Class.eq fun _ => Range.inv_exclude_singular ff h1

theorem dom_complete_is_complete : dom μ = μ := Class.eq fun _ => Iff.intro
  (fun h => Class.in_complete.mpr (Ensemble.intro h))
  (fun h => have ens := Ensemble.intro h; Domain.intro (Class.in_complete.mpr (Ensemble.map_ordered ens ens)))

theorem ran_complete_is_complete : ran μ = μ := Class.eq fun _ => Iff.intro
  (fun h => Class.in_complete.mpr (Ensemble.intro h))
  (fun h => have ens := Ensemble.intro h; Range.intro (Class.in_complete.mpr (Ensemble.map_ordered ens ens)))

noncomputable def raw_value (f x : Class) := Classify fun y => (x, y) ∈ f
noncomputable def Value f x := ∩ raw_value f x
noncomputable def val := Value

theorem out_of_domain_val_is_complete : x ∉ dom f → val f x = μ := fun h =>
  have h1 : raw_value f x = Φ := Classical.byContradiction fun f =>
    have ⟨y, f1⟩ := sib_exist_non_empty.mp f
    have ⟨_, f2⟩ := Class.classify.mp f1; h (Domain.intro f2)
  by show ∩ raw_value f x = μ; rw[h1]; exact sinter_empty_is_complete_eq

theorem in_domain_val_is_ens: x ∈ dom f → Ensemble (val f x) := fun h =>
  have ⟨_, ⟨y, h1⟩⟩ := Class.classify.mp h
  sinter_ens_non_empty (sib_exist_non_empty.mpr ⟨y, Class.classify.mpr ⟨Ensemble.unwrap_ordered_r (Ensemble.intro h1), h1⟩⟩)

theorem complete_val_is_out_of_domain: val f x = μ → x ∉ dom f := fun h => Not.intro fun f1 =>
  have ens := in_domain_val_is_ens f1; by rw[h] at ens; exact complete_nens ens

theorem ens_val_is_in_domain : Ensemble (val f x) → x ∈ dom f := fun h => Classical.byContradiction fun f1 =>
  have f2 := out_of_domain_val_is_complete f1; by rw[f2] at h; exact complete_nens h

theorem fn_val_intro : Function f → (x, y) ∈ f → val f x = y := fun ff h => Class.eq fun z => Iff.intro
  (fun h1 => (Class.classify.mp h1).right y (Class.classify.mpr ⟨Ensemble.unwrap_ordered_r (Ensemble.intro h), h⟩))
  (fun h1 => Class.classify.mpr ⟨Ensemble.intro h1, fun w h2 =>
    have ⟨_, h3⟩ := Class.classify.mp h2; have h4 := Function.yeq ff h h3; by rw[h4] at h1; exact h1⟩)

theorem fn_val_mp : z ∈ val f x → (∀ y, (x, y) ∈ g → (x, y) ∈ f) → z ∈ val g x := fun h conv =>
  Class.classify.mpr ((Class.classify.mp h).imp_right fun f1 y => have f1' := f1 y;
    fun h => f1' (Class.classify.mpr ((Class.classify.mp h).imp_right (conv y))))

theorem fn_val_singleton: Ensemble a → Ensemble b → val {(a, b)} a = b := fun ea eb => Class.eq fun x => Iff.intro
  (fun h => (Class.classify.mp h).right b (Class.classify.mpr ⟨eb, Class.in_singleton (Ensemble.map_ordered ea eb)⟩))
  (fun h => Class.classify.mpr ⟨Ensemble.intro h, fun y h1 =>
    have ⟨_, h1⟩ := Class.classify.mp h1; have ⟨_, eq⟩ := singleton_ordered_rfl ea eb h1
    by rw[eq]; exact h⟩)

theorem fn_val_elim_singular : Ensemble a → Ensemble b → a ∉ dom f → x ∈ dom f → val (f ∪ {(a, b)}) x = val f x :=
  fun ea eb h1 h2 => Class.eq fun z => Iff.intro
    (fun h3 => fn_val_mp h3 fun y h => Union.intro (Or.inl h))
    (fun h3 => fn_val_mp h3 fun y h => (Union.split h).resolve_right fun f2 =>
      have ⟨eq_ab, _⟩ := singleton_ordered_rfl ea eb f2; by rw[← eq_ab] at h1; exact h1 h2)

theorem fn_val_include_singular : Ensemble a → Ensemble b → a ∉ dom f → val (f ∪ {(a, b)}) a = b :=
  fun ea eb h =>
    have eq1 : val (f ∪ {(a, b)}) a = val {(a, b)} a := Class.eq fun _ => Iff.intro
      (fun h1 => fn_val_mp h1 fun _ h2 => Union.intro (Or.inr h2))
      (fun h1 => fn_val_mp h1 fun _ h2 => (Union.split h2).resolve_left fun fake => h (Domain.intro fake))
    eq1.trans (fn_val_singleton ea eb)

theorem fn_graph_eq : Function f → f = PairedClassify fun x y => val f x = y := fun ff => Class.paired_eq
  ff.left PairedClassify.relative fun x y => Iff.intro
    (fun h => Class.paired_classify.mpr ⟨Ensemble.intro h, fn_val_intro ff h⟩)
    (fun h => by
      have ⟨ens, eq1⟩ := Class.paired_classify.mp h; rw[← eq1]; rw[← eq1] at ens
      have ⟨_, ⟨y, d⟩⟩ := Class.classify.mp (ens_val_is_in_domain (Ensemble.unwrap_ordered_r ens))
      have eq2 := fn_val_intro ff d; rw[eq2]; exact d)

theorem fn_val_unwrap : Function f → Ensemble x → Ensemble y → val f x = y → (x, y) ∈ f := fun ff ex ey h => by
  have h1 := fn_graph_eq ff; rw[h1]; exact Class.paired_classify.mpr ⟨Ensemble.map_ordered ex ey, h⟩

theorem fn_val_rfl : Function f → x ∈ dom f → (x, val f x) ∈ f := fun ff h => by
  have eq1 := fn_graph_eq ff; rw (occs := [1]) [eq1]
  exact Class.paired_classify.mpr ⟨Ensemble.map_ordered (Ensemble.intro h) (in_domain_val_is_ens h), rfl⟩

theorem fn_val_rfl_ran : Function f → val f x ∈ ran f → (x, val f x) ∈ f := fun ff h =>
  fn_val_rfl ff (ens_val_is_in_domain (Ensemble.intro h))

theorem fn_subval : Function f → Function g → f ⊆ g → ∀ x, x ∈ dom f → val f x = val g x :=
  fun ff fg ss x d => Class.eq fun u => Iff.intro
    (fun h => fn_val_mp h fun y h =>
      have ⟨_, ⟨z, h1⟩⟩ := Class.classify.mp d; have h2 := Function.yeq fg h (apply_subset ss h1)
      by rw[← h2] at h1; exact h1)
    (fun h => fn_val_mp h fun y h => apply_subset ss h)

theorem fn_dom_to_val_ran : Function f → x ∈ dom f → val f x ∈ ran f := fun ff h =>
  Range.intro (fn_val_rfl ff h)

theorem Function.eq : Function f → Function g → (∀ x, val f x = val g x) → f = g :=
  fun ff fg h => Class.paired_eq ff.left fg.left fun x _ => Iff.intro
    (fun h1 => have h2 := fn_val_intro ff h1; have ⟨ex, ey⟩ := Ensemble.unwrap_ordered (Ensemble.intro h1)
      fn_val_unwrap fg ex ey ((h x).symm.trans h2))
    (fun h1 => have h2 := fn_val_intro fg h1; have ⟨ex, ey⟩ := Ensemble.unwrap_ordered (Ensemble.intro h1)
      fn_val_unwrap ff ex ey ((h x).trans h2))

axiom Ensemble.map_dom_to_ran : Function f → Ensemble (dom f) → Ensemble (ran f)
axiom Ensemble.map_sunion : Ensemble x → Ensemble (∪x)

variable {u v : Class}

noncomputable def Cartesian (x y : Class) := PairedClassify fun u v => u ∈ x ∧ v ∈ y
infixr:60 " × " => Cartesian

noncomputable def ycsn (u y : Class) := PairedClassify fun w z => w ∈ y ∧ z = (u, w)

theorem ycsn_prop_fn : Function (ycsn u y) :=
  ⟨PairedClassify.relative, fun _ _ _ h1 h2 =>
    have eq1 := (Class.paired_classify.mp h1).right.right
    have eq2 := (Class.paired_classify.mp h2).right.right
    eq1.trans eq2.symm⟩

theorem ycsn_prop_dom : Ensemble u → dom (ycsn u y) = y := fun eu => Class.eq fun _ => Iff.intro
  (fun h => have ⟨_, ⟨_, h1⟩⟩ := Class.classify.mp h; have ⟨_, ⟨h2, _⟩⟩ := Class.paired_classify.mp h1; h2)
  (fun h => have ex := Ensemble.intro h
    Domain.intro (Class.paired_classify.mpr ⟨Ensemble.map_ordered ex (Ensemble.map_ordered eu ex), ⟨h, rfl⟩⟩))

theorem ycsn_prop_ran_relative : Relation (ran (ycsn u y)) := fun _ h =>
  have ⟨_, ⟨v, h1⟩⟩ := Class.classify.mp h; have ⟨_, ⟨_, h2⟩⟩ := Class.paired_classify.mp h1
  ⟨u, ⟨v, h2⟩⟩

theorem ycsn_prop_ran : Ensemble u → Ensemble y → ran (ycsn u y) = {u} × y :=
  fun eu ey => Class.paired_eq ycsn_prop_ran_relative PairedClassify.relative fun a b => Iff.intro
    (fun h => have ⟨ens, ⟨v, h1⟩⟩ := Class.classify.mp h; have ⟨_, ⟨h2, h3⟩⟩ := Class.paired_classify.mp h1
      have ⟨eq_au, eq_bv⟩ := (ordered_rfl (Ensemble.unwrap_ordered ens)).mp h3
      Class.paired_classify.mpr ⟨ens,
        ⟨singleton_eq' (Ensemble.unwrap_ordered_l ens) eq_au, by rw[← eq_bv] at h2; exact h2⟩⟩)
    (fun h => have ⟨ens, ⟨h1, h2⟩⟩ := Class.paired_classify.mp h
      Range.intro (Class.paired_classify.mpr ⟨Ensemble.map_ordered (Ensemble.intro h2) ens,
        ⟨h2, by rw[singleton_eq eu h1]⟩⟩))

theorem Ensemble.map_cart_sn : Ensemble u → Ensemble y → Ensemble ({u} × y) := fun eu ey => by
  rw[← ycsn_prop_ran eu ey]; apply map_dom_to_ran
  · exact ycsn_prop_fn
  · rw[ycsn_prop_dom eu]; exact ey

noncomputable def ycsns (x y : Class) := PairedClassify fun u z => u ∈ x ∧ z = {u} × y
noncomputable def ycsns_ran (x y : Class) := Classify fun z => ∃ u, u ∈ x ∧ z = {u} × y

theorem ycsns_prop_fn : Function (ycsns x y) :=
  ⟨PairedClassify.relative, fun _ _ _ h1 h2 =>
    have eq1 := (Class.paired_classify.mp h1).right.right
    have eq2 := (Class.paired_classify.mp h2).right.right
    eq1.trans eq2.symm⟩

theorem ycsns_prop_dom : Ensemble y → dom (ycsns x y) = x := fun ey => Class.eq fun _ => Iff.intro
  (fun h => have ⟨_, _, h1⟩ := Class.classify.mp h; have ⟨_, ⟨h2, _⟩⟩ := Class.paired_classify.mp h1; h2)
  (fun h => have ez := Ensemble.intro h;
    Domain.intro (Class.paired_classify.mpr ⟨Ensemble.map_ordered ez (Ensemble.map_cart_sn ez ey), h, rfl⟩))

theorem ycsns_prop_ran : ran (ycsns x y) = ycsns_ran x y := Class.eq fun _ => Iff.intro
  (fun h =>
    have ⟨ez, a, h1⟩ := Class.classify.mp h
    have ⟨_, h2, h3⟩ := Class.paired_classify.mp h1
    Class.classify.mpr ⟨ez, ⟨a, h2, h3⟩⟩)
  (fun h =>
    have ⟨ez, _, h1, h2⟩ := Class.classify.mp h
    Range.intro (Class.paired_classify.mpr ⟨Ensemble.map_ordered (Ensemble.intro h1) ez, h1, h2⟩))

theorem ycsns_ran_prop_sunion_relative : Relation (∪ycsns_ran x y) := fun z h => by
  have ⟨ez, a, h1, h2⟩ := Class.classify.mp h
  have ⟨ea, b, h3, h4⟩ := Class.classify.mp h2
  rw[h4] at h1; exact PairedClassify.relative z h1

theorem ycsns_prop_sunion_eq : Ensemble y → ∪ycsns_ran x y = x × y :=
  fun ey => Class.paired_eq ycsns_ran_prop_sunion_relative PairedClassify.relative fun u v => Iff.intro
    (fun h => by
      have ⟨eab, a, h2, h3⟩ := Class.classify.mp h
      have ⟨ea, z, h4, h5⟩ := Class.classify.mp h3; rw[h5] at h2
      have ⟨euv, h6, h7⟩ := Class.paired_classify.mp h2
      have eq_uz := singleton_eq (Ensemble.intro h4) h6; rw[← eq_uz] at h4
      exact Class.paired_classify.mpr ⟨euv, h4, h7⟩)
    (fun h => have ⟨euv, h1, h2⟩ := Class.paired_classify.mp h
      Class.classify.mpr ⟨euv, {u} × y, Class.paired_classify.mpr
        ⟨euv, Class.in_singleton (Ensemble.unwrap_ordered_l euv), h2⟩,
          Class.classify.mpr ⟨Ensemble.map_cart_sn (Ensemble.intro h1) ey, u, h1, rfl⟩⟩)

theorem Ensemble.map_cart : Ensemble x → Ensemble y → Ensemble (x × y) := fun ex ey => by
  have eq1 : ∪ycsns_ran x y = x × y := ycsns_prop_sunion_eq ey; rw[← eq1]
  apply Ensemble.map_sunion; rw[← ycsns_prop_ran]; apply Ensemble.map_dom_to_ran
  · exact ycsns_prop_fn
  · rw[ycsns_prop_dom ey]; exact ex

theorem Ensemble.map_dom_to_fn : Function f → Ensemble (dom f) → Ensemble f := fun ff ed =>
  (Ensemble.map_cart ed (Ensemble.map_dom_to_ran ff ed)).mp (subset_paired_intro ff.left fun _ _ h =>
    Class.paired_classify.mpr ⟨Ensemble.intro h, Domain.intro h, Range.intro h⟩)

theorem Ensemble.map_fn_to_dom : Function f → Ensemble f → Ensemble (dom f) := fun ff ef =>
  let g := PairedClassify fun u v => u ∈ f ∧ v = First u
  have fg : Function g := ⟨PairedClassify.relative, fun _ _ _ h1 h2 =>
    have ⟨_, _, eq1⟩ := Class.paired_classify.mp h1
    have ⟨_, _, eq2⟩ := Class.paired_classify.mp h2
    eq1.trans eq2.symm⟩
  have g_dom_relative : Relation (dom g) := fun z h =>
    have ⟨_, _, h1⟩ := Class.classify.mp h
    have ⟨_, h2, _⟩ := Class.paired_classify.mp h1
    ff.left z h2
  have g_dom_is_f : dom g = f := Class.paired_eq g_dom_relative ff.left fun x y => Iff.intro
    (fun h => have ⟨_, _, h1⟩ := Class.classify.mp h
      have ⟨_, h2, _⟩ := Class.paired_classify.mp h1; h2)
    (fun h => have exy := Ensemble.intro h
      Domain.intro (Class.paired_classify.mpr ⟨Ensemble.map_ordered exy (Ensemble.unwrap_ordered_l exy),
        h, (unwrap_ordered_first (Ensemble.unwrap_ordered exy)).symm⟩))
  have g_ran_is_f_dom : ran g = dom f := Class.eq fun y => Iff.intro
    (fun h => by
      have ⟨_, x, h1⟩ := Class.classify.mp h; have ⟨exy, h2, h3⟩ := Class.paired_classify.mp h1
      have euv := Ensemble.unwrap_ordered_l exy; have ⟨u, v, eq1⟩ := ff.left x h2;
      rw[eq1] at h3; rw[eq1] at euv; rw[eq1] at h2
      have eq2 := unwrap_ordered_first (Ensemble.unwrap_ordered euv); rw[eq2] at h3; rw[h3]
      exact Domain.intro h2)
    (fun h => have ⟨ey, x, h1⟩ := Class.classify.mp h
      Range.intro (Class.paired_classify.mpr ⟨Ensemble.map_ordered (Ensemble.intro h1) ey,
        h1, (unwrap_ordered_first (Ensemble.unwrap_ordered (Ensemble.intro h1))).symm⟩))
  by rw[← g_ran_is_f_dom]; apply Ensemble.map_dom_to_ran; exact fg; rw[g_dom_is_f]; exact ef

theorem Ensemble.map_fn_to_ran : Function f → Ensemble f → Ensemble (ran f) := fun ff ef =>
  Ensemble.map_dom_to_ran ff (Ensemble.map_fn_to_dom ff ef)

noncomputable def Exponent y x := Classify fun f => Function f ∧ dom f = x ∧ ran f ⊆ y

theorem Ensemble.map_exponent : Ensemble x → Ensemble y → Ensemble (Exponent y x) := fun ex ey =>
  have ss : Exponent y x ⊆ pow (x × y) := fun f h =>
    have ⟨ef, ff, h1, h2⟩ := Class.classify.mp h
    Class.classify.mpr ⟨ef, subset_paired_intro ff.left fun u v h => by
      rw[← h1]
      exact Class.paired_classify.mpr ⟨Ensemble.intro h, Domain.intro h, apply_subset h2 (Range.intro h)⟩⟩
  Ensemble.mp (Ensemble.map_pow (Ensemble.map_cart ex ey)) ss

def On f x := Function f ∧ dom f = x
def To f y := Function f ∧ ran f ⊆ y
def Onto f y := Function f ∧ ran f = y

variable {n r: Class}

def RRelation (x r y : Class) := (x, y) ∈ r
def rrel := RRelation
def Connect (r x : Class) := ∀ u v, u ∈ x → v ∈ x → rrel u r v ∨ rrel v r u ∨ u = v
def Transitive (r x : Class) := ∀ u v w, u ∈ x → v ∈ x → w ∈ x → rrel u r v → rrel v r w → rrel u r w
def Asymmetric (r x : Class) := ∀ u v, u ∈ x → v ∈ x → rrel u r v → ¬rrel v r u

def Asymm := Asymmetric

theorem asymm_rfl : Asymm r x → u ∈ x → ¬rrel u r u := fun h1 h2 fake => (h1 u u h2 h2 fake) fake

def FirstMember (z r x : Class) := z ∈ x ∧ (∀ y, y ∈ x → ¬rrel y r z)
def WellOrdered r x := Connect r x ∧ (∀ y, y ⊆ x → y ≠ Φ → ∃ z, FirstMember z r y)

theorem Connect.mp : Connect r x → y ⊆ x → Connect r y := fun h ss u v h1 h2 =>
  h u v (apply_subset ss h1) (apply_subset ss h2)

theorem WellOrdered.mp : WellOrdered r x → y ⊆ x → WellOrdered r y := fun h ss =>
  ⟨Connect.mp h.left ss, fun z zss zne => h.right z (subset_trans zss ss) zne⟩

theorem Connect.resolve : Connect r x → u ∈ x → v ∈ x → ¬rrel u r v → rrel v r u ∨ u = v :=
  fun c ux vx h => (c u v ux vx).resolve_left h

def Asymm.elim {α} : Asymm r x → u ∈ x → v ∈ x → rrel u r v → rrel v r u → α :=
  fun as ux vx h1 h2 => (as u v ux vx h1).elim h2

theorem WellOrdered.asymm : WellOrdered r x → Asymm r x := fun h u v h1 h2 h3 =>
  have eu := Ensemble.intro h1; have ev := Ensemble.intro h2;
  have uv1 : {u, v} ⊆ x := fun z j =>
    have j1 := (pick_from_unordered_iff eu ev z).mp j
    j1.elim (fun eq => by rw[eq]; exact h1) (fun eq => by rw[eq]; exact h2) 
  have uv2 : {u, v} ≠ Φ := fun fake => by
    have j : u ∈ {u, v} := in_unordered eu; rw[fake] at j
    exact Class.not_in_empty j
  fun fake =>
    have ⟨z, h4, h5⟩ := h.right {u, v} uv1 uv2
    have h4 := pick_from_unordered eu ev h4
    h4.elim
      (fun a => by rw[← a] at fake; exact h5 v (in_unordered' ev) fake)
      (fun a => by rw[← a] at h3; exact h5 u (in_unordered eu) h3)

theorem WellOrdered.transitive : WellOrdered r x → Transitive r x := fun h u v w hu hv hw r1 r2 =>
  have eu := Ensemble.intro hu; have ev := Ensemble.intro hv; have ew := Ensemble.intro hw;
  have h1 : {u, v, w} ⊆ x := fun z j =>
    let conv {a : Class} : a ∈ x → z ∈ ({a} : Class) → z ∈ x := fun h1 h2 => by
      have eq := singleton_eq (Ensemble.intro h1) h2; rw[eq]; exact h1
    (Union.split j).elim (conv hu) fun j1 => (Union.split j1).elim (conv hv) (conv hw)
  have h2 : {u, v, w} ≠ Φ := fun fake => by
    have j : u ∈ {u, v, w} := Union.intro (Or.inl (Class.in_singleton eu)); rw[fake] at j
    exact Class.not_in_empty j
  have ⟨z, h3, h4⟩ := h.right {u, v, w} h1 h2
  match pick_from_unordered3 eu ev ew h3 with
  | Or.inl h5 => by
    rw[h5] at h4; have h5 := h.left.resolve hw hu (h4 w (in_unordered3'' ew))
    exact h5.elim id fun eq => by rw[eq] at r2; exact h.asymm.elim hu hv r1 r2
  | Or.inr (Or.inl h5) => by rw[h5] at h4; exact (h4 u (in_unordered3 eu)).elim r1
  | Or.inr (Or.inr h5) => by rw[h5] at h4; exact (h4 v (in_unordered3' ev)).elim r2

def RSection y r x := y ⊆ x ∧ WellOrdered r x ∧ (∀ u v, u ∈ x → v ∈ y → rrel u r v → u ∈ y)
def rseg := RSection

theorem RSection.map_sinter : n ≠ Φ → (∀ y, y ∈ n → rseg y r x) → rseg (∩n) r x := fun nne h =>
  have ⟨a, h1⟩ := sib_exist_non_empty.mp nne; have ⟨h2, h3, _⟩ := h a h1
  ⟨fun _ j => apply_subset h2 ((Class.classify.mp j).right a h1), h3,
    fun u v j1 j2 j3 => Class.classify.mpr ⟨Ensemble.intro j1, fun y j4 =>
      have ⟨_, _, h4⟩ := h y j4; have ⟨_, j2'⟩ := Class.classify.mp j2; have j2' := j2' y j4
      h4 u v j1 j2' j3⟩⟩

theorem RSection.map_sunion : n ≠ Φ → (∀ y, y ∈ n → rseg y r x) → rseg (∪n) r x := fun nne h =>
  have ⟨a, h1⟩ := sib_exist_non_empty.mp nne; have ⟨_, h3, _⟩ := h a h1
  ⟨fun _ j => have ⟨_, y, j1, j2⟩ := Class.classify.mp j; have ⟨h2, _, _⟩ := h y j2; apply_subset h2 j1, h3,
    fun u v j1 j2 j3 => have ⟨_, z, j4, j5⟩ := Class.classify.mp j2; have ⟨_, _, h4⟩ := h z j5
      Class.classify.mpr ⟨Ensemble.intro j1, z, h4 u v j1 j4 j3, j5⟩⟩
