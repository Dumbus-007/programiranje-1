set_option autoImplicit false

/------------------------------------------------------------------------------
 ## Naravna števila

 Definirajte funkcijo, ki _rekurzivno_ (torej naivno in ne direktno s formulo,
 ki jo boste morali dokazati) sešteje prvih `n` naravnih števil, ter
 dokažite, da zanjo velja znana enakost (najprej v obliki, ki ne zahteva
 deljenja, nato pa še v običajni obliki).
------------------------------------------------------------------------------/

def vsota_prvih : Nat → Nat :=
  fun n =>
  match n with
  |0 => 0
  |k => if k > 0 then k + vsota_prvih (k-1) else 0

theorem gauss : (n : Nat) → 2 * vsota_prvih n = n * (n + 1) :=
by
  intro n
  induction n with
  |zero => simp [vsota_prvih]
  |succ n ih =>
    simp [vsota_prvih]
    rw [Nat.mul_add]
    rw [ih]
    calc
      2 * (n + 1) + n * (n + 1)
        = (n + 1) * 2 + (n + 1) * n := by simp [Nat.mul_comm]
        _ = (n+1)* (n+2) := by rw [Nat.mul_add, Nat.add_comm]


theorem cisto_pravi_gauss : (n : Nat) → vsota_prvih n = (n * (n + 1)) / 2 := by
  intro n
  induction n with
  |zero => simp [vsota_prvih]
  |succ n ih =>
    simp [vsota_prvih]
    rw [ih]
    -- calc
    --   n +1 + n * (n+1) / 2
    --   = 2 * (n+1) / 2 + n * (n+1)/2 := by simp []
    --   _ = (2 * (n + 1) + n * (n+1)) / 2 := by rw [← add_div]




/------------------------------------------------------------------------------
 ## Vektorji

 Definirajmo vektorje podobno kot na predavanjih, le da namesto svojih naravnih
 števil uporabimo vgrajena. Da se tipi ujamejo, funkcijo stikanja napišemo s
 pomočjo taktik.

 Napišite funkcijo `obrni`, ki vrne na glavo obrnjen vektor, ter funkciji
 `glava` in `rep`, ki varno vrneta glavo in rep _nepraznega_ seznama.
------------------------------------------------------------------------------/

inductive Vektor : Type → Nat → Type where
  | prazen : {A : Type} → Vektor A 0
  | sestavljen : {A : Type} → {n : Nat} → A → Vektor A n → Vektor A (n + 1)
deriving Repr

def stakni : {A : Type} → {m n : Nat} → Vektor A m → Vektor A n → Vektor A (m + n) :=
  fun xs ys => match xs with
  | .prazen => by rw [Nat.add_comm]; exact ys
  | .sestavljen x xs' => by rw [Nat.add_right_comm]; exact Vektor.sestavljen x (stakni xs' ys)

def pomozna_za_obrni: {A: Type} -> {m n : Nat} -> Vektor A m -> Vektor A n -> Vektor A (m+n) :=
fun vec acc =>
  match vec with
  |.prazen => by rw [Nat.add_comm]; exact acc
  |.sestavljen x xs => pomozna_za_obrni xs (Vektor.sestavljen x acc)


def obrni : {A : Type} → {n : Nat} → Vektor A n → Vektor A n :=
  fun vec =>
  pomozna_za_obrni vec Vektor.prazen

-- v navodilih piše, da vračamo glavo in rep _seznama_. Če je bilo mišljeno
-- zares na seznamih, potem sta to tidve funkciji:

def glava' : {A: Type} -> List A -> Option A :=
  fun sez =>
  match sez with
  |[] => none
  |x::_ => some x

def rep' : {A: Type} -> List A -> Option (List A) :=
  fun sez =>
  match sez with
  |[] => none
  |_::xs => some xs

-- Če pa gre za napako in bi moralo pisati _vektor_ (ker smo namreč v
-- podpoglavju vektorjev), pa sta to potem tidve funkciji:

def glava : {A : Type} → {n : Nat} → Vektor A n → Option A :=
fun vec =>
match vec with
| .prazen => none
| .sestavljen x _ => some x

def rep : {A : Type} → {n : Nat} → Vektor A n → Option (Vektor A (n - 1)) :=
fun vec =>
match vec with
| .prazen => none
| .sestavljen _ xs => some xs

/------------------------------------------------------------------------------
 ## Predikatni račun

 Dokažite spodnje tri trditve. Zadnja je _paradoks pivca_, ki pravi:
   "V vsaki neprazni gostilni obstaja gost, za katerega velja,
   da če pije on, pijejo vsi v gostilni."
 Za dokaz potrebujete klasično logiko, torej nekaj iz modula `Classical`.
------------------------------------------------------------------------------/

theorem forall_implies : {A : Type} → {P Q : A → Prop} →
  (∀ x, (P x → Q x)) → (∀ x, P x) → (∀ x, Q x) := by
  intro x P Q h1 h2
  intro x
  apply h1
  apply h2

theorem forall_implies' : {A : Type} → {P : Prop} → {Q : A → Prop} →
  (∀ x, (P → Q x)) ↔ (P → ∀ x, Q x) := by
  intros x P Q
  constructor
  intro h1
  intro P x
  apply h1
  exact P

  intro h2
  intro x P
  apply h2
  exact P


theorem paradoks_pivca :
  {G : Type} → {P : G → Prop} →
  (g : G) →  -- (g : G) pove, da je v gostilni vsaj en gost
  ∃ (p : G), (P p → ∀ (x : G), P x) := by
  intro G P g
  exists g
  intro H_g_pije x
  -- fomck

/------------------------------------------------------------------------------
 ## Dvojiška drevesa

 Podan naj bo tip dvojiških dreves skupaj s funkcijama za zrcaljenje in izračun
 višine ter dvema funkcijama, ki obe od leve proti desni naštejeta elemente
 drevesa. Pri tem prva deluje naivno in ima časovno zahtevnost O(n log n), druga
 pa je malo bolj zapletena in deluje v času O(n). Dokažite spodnje enakosti, pri
 čemer lahko do pomožne funkcije `aux` dostopate kot `elementi'.aux`
-------------------------------------------------------------------------------/

inductive Drevo : Type → Type where
  | prazno : {A : Type} → Drevo A
  | sestavljeno : {A : Type} → Drevo A → A → Drevo A → Drevo A

def zrcali : {A : Type} → Drevo A → Drevo A :=
  fun t => match t with
  | .prazno => .prazno
  | .sestavljeno l x d => .sestavljeno (zrcali d) x (zrcali l)

def visina : {A : Type} → Drevo A → Nat :=
  fun t => match t with
  | .prazno => 0
  | .sestavljeno l _ d => 1 + max (visina l) (visina d)

def elementi : {A : Type} → Drevo A → List A :=
  fun t => match t with
  | .prazno => []
  | .sestavljeno l x d => elementi l ++ x :: elementi d

def elementi' : {A : Type} → Drevo A → List A :=
  let rec aux : {A : Type} → Drevo A → List A → List A :=
    fun t acc => match t with
    | .prazno => acc
    | .sestavljeno l x d => aux l (x :: aux d acc)
  fun t => aux t []

theorem zrcali_zrcali :
  {A : Type} → (t : Drevo A) →
  zrcali (zrcali t) = t := by
  intro A t
  induction t with
  | prazno => simp [zrcali]
  | sestavljeno l g d leva_ih desna_ih =>
    simp [zrcali]
    constructor
    apply leva_ih
    apply desna_ih

theorem visina_zrcali :
  {A : Type} → (t : Drevo A) →
  visina (zrcali t) = visina t := by
  intro A t
  induction t with
  | prazno => simp [zrcali]
  | sestavljeno l g d leva_ih desna_ih =>
  simp [visina]
  rw [leva_ih, desna_ih]
  rw [Nat.max_comm]


theorem za_vsak_acc_v_aux: {A: Type} -> (t:Drevo A) -> (acc1 acc2: List A) ->
  elementi'.aux t (acc1 ++ acc2) = elementi'.aux t acc1 ++ acc2 := by
  intros A t
  induction t with
  |prazno =>
    intro acc1 acc2
    simp [elementi'.aux]
  |sestavljeno l x d leva_ih desna_ih =>
  intro acc1 acc2
  simp [elementi'.aux]
  rw [desna_ih]
  rw [← leva_ih]
  rfl

theorem elementi_elementi' :
  {A : Type} → (t : Drevo A) →
  elementi t = elementi' t := by
  intro A t
  induction t with
  |prazno => simp [elementi, elementi', elementi'.aux]
  |sestavljeno l x d leva_ih desna_ih =>
  simp [elementi, elementi', elementi'.aux]
  rw [leva_ih, desna_ih]
  simp [elementi', elementi'.aux]
  rw [← za_vsak_acc_v_aux]
  rfl
