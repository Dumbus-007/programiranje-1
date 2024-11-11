(*----------------------------------------------------------------------------*
   # Abstrakcija
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
   ## Naravna števila
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
   Definirajte signaturo `NAT`, ki določa strukturo naravnih števil. Ima osnovni
   tip, funkcijo enakosti, ničlo in enko, seštevanje, odštevanje in množenje.
   Hkrati naj vsebuje pretvorbe iz in v OCamlov `int` tip. Opomba: Funkcije za
   pretvarjanje ponavadi poimenujemo `to_int` and `of_int`, tako da skupaj z
   imenom modula dobimo ime `NAT.of_int`, ki nam pove, da pridobivamo naravno
   število iz celega števila.
  [*----------------------------------------------------------------------------*)

module type NAT = sig
  type t

  val eq : t -> t -> bool
  val zero : t
  val one : t
  val sestej : t -> t -> t
  val odstej : t -> t -> t
  val zmnozi : t -> t -> t
  val to_int : t -> int
  val of_int : int -> t
end

(*----------------------------------------------------------------------------*
   Napišite implementacijo modula `Nat_int`, ki zgradi modul s signaturo `NAT`,
   kjer kot osnovni tip uporablja OCamlov tip `int`. Namig: dokler ne
   implementirate vse funkcij v `Nat_int`, se bo OCaml pritoževal. Temu se lahko
   izognete tako, da funkcije, ki še niso napisane nadomestite z `failwith
   "later"`, vendar to ne deluje za konstante.
  [*----------------------------------------------------------------------------*)

module Nat_int : NAT = struct
  type t = int

  let eq x y = x = y
  let zero = 0
  let one = 1
  let sestej x y = x + y
  let odstej x y = if x > y then x - y else 0
  let zmnozi x y = x * y
  let to_int x = x
  let of_int x = if x > 0 then x else 0
end

(*----------------------------------------------------------------------------*
   Napišite implementacijo `NAT`, ki temelji na [Peanovih
   aksiomih](https://en.wikipedia.org/wiki/Peano_axioms). Osnovni tip modula
   definirajte kot naštevni tip, ki vsebuje konstruktor za ničlo in konstruktor za
   naslednika nekega naravnega števila. Večino funkcij lahko implementirate s
   pomočjo rekurzije. Naprimer, enakost števil `k` in `l` določimo s hkratno
   rekurzijo na `k` in `l`, kjer je osnoven primer `Zero = Zero`.
  [*----------------------------------------------------------------------------*)

module Nat_peano : NAT = struct
  type t = Zero | Succ of t

  let rec eq x y =
    match (x, y) with
    | Zero, Zero -> true
    | Succ _, Zero -> false
    | Zero, Succ _ -> false
    | Succ x', Succ y' -> eq x' y'

  let zero = Zero
  let one = Succ Zero

  let to_int x =
    let rec aux acc = function Zero -> acc | Succ x' -> aux (acc + 1) x' in
    aux 0 x

  let of_int x =
    let rec aux x =
      match x with
      | 0 -> zero
      | 1 -> one
      | k when k < 0 -> zero
      | k -> Succ (aux (k - 1))
    in
    aux x

  let rec sestej x y =
    match (x, y) with
    | Zero, k -> k
    | k, Zero -> k
    | Succ k, Succ l -> Succ (sestej k l)

  let rec odstej x y =
    match (x, y) with
    | Zero, Zero -> Zero
    | Zero, k -> Zero
    | k, Zero -> k
    | Succ x', Succ y' -> odstej x' y'

  let rec zmnozi x y =
    match (x, y) with
    | Zero, Zero -> Zero
    | Zero, k -> Zero
    | k, Zero -> Zero
    | Succ x', y -> sestej y (zmnozi x' y)
end

(*----------------------------------------------------------------------------*
   Z ukazom `let module ImeModula = ... in ...` lahko modul definiramo samo
   lokalno. To bomo uporabili za to, da bomo lahko enostavno preklapljali med
   moduloma `Nat_int` in `Nat_peano`, saj bomo enega ali drugega shranili pod ime
   `Nat`. OCaml sicer pozna tudi ustrezne abstrakcije, ki omogočijo preklapljanje
   med moduli, na primer [funktorje](https://ocaml.org/docs/functors) ali
   [prvorazredne module](https://ocaml.org/manual/5.2/firstclassmodules.html), a
   bomo uporabili preprostejšo rešitev.

   Spodnji izračun dopolnite tako, da sešteje prvih 100 naravnih števil. Ker bo
   taka vsota tipa `NAT.t`, ki je abstrakten, končni rezultat pretvorite v tip
   `int` z uporabo funkcije `Nat.to_int`. Če ste oba modula implementirali
   pravilno, bi morali dobiti enak rezultat ne glede na to, katerega poimenujete
   `Nat`.
  [*----------------------------------------------------------------------------*)

let sum_nat_100 =
  let module Nat = Nat_peano in
  let rec pomozna : Nat.t -> int -> int =
   fun x acc ->
    if Nat.eq x Nat.zero then acc else pomozna (Nat.odstej x Nat.one) (acc + 1)
  in
  pomozna (Nat.of_int 100) 0

(* |> Nat.to_int *)
(* val sum_nat_100 : int = 5050 *)

(*----------------------------------------------------------------------------*
   ## Kompleksna števila
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
   > Once upon a time, there was a university with a peculiar tenure
   > policy. All faculty were tenured, and could only be dismissed for
   > moral turpitude. What was peculiar was the definition of moral
   > turpitude: making a false statement in class. Needless to say, the
   > university did not teach computer science. However, it had a renowned
   > department of mathematics.
   >
   > One Semester, there was such a large enrollment in complex variables
   > that two sections were scheduled. In one section, Professor Descartes
   > announced that a complex number was an ordered pair of reals, and that
   > two complex numbers were equal when their corresponding components
   > were equal. He went on to explain how to convert reals into complex
   > numbers, what "i" was, how to add, multiply, and conjugate complex
   > numbers, and how to find their magnitude.
   >
   > In the other section, Professor Bessel announced that a complex number
   > was an ordered pair of reals the first of which was nonnegative, and
   > that two complex numbers were equal if their first components were
   > equal and either the first components were zero or the second
   > components differed by a multiple of 2π. He then told an entirely
   > different story about converting reals, "i", addition, multiplication,
   > conjugation, and magnitude.
   >
   > Then, after their first classes, an unfortunate mistake in the
   > registrar's office caused the two sections to be interchanged. Despite
   > this, neither Descartes nor Bessel ever committed moral turpitude,
   > even though each was judged by the other's definitions. The reason was
   > that they both had an intuitive understanding of type. Having defined
   > complex numbers and the primitive operations upon them, thereafter
   > they spoke at a level of abstraction that encompassed both of their
   > definitions.
   >
   > The moral of this fable is that: Type structure is a syntactic
   > discipline for enforcing levels of abstraction.
   >
   > John C. Reynolds, _Types, Abstraction, and Parametric Polymorphism_, IFIP83
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
   Definirajte signaturo modula kompleksnih števil. Potrebujemo osnovni tip, test
   enakosti, ničlo, enko, imaginarno konstanto i, negacijo, konjugacijo,
   seštevanje in množenje.
  [*----------------------------------------------------------------------------*)

module type COMPLEX = sig
  type t

  val eq : t -> t -> bool
  (* Dodajte manjkajoče! *)
end

(*----------------------------------------------------------------------------*
   Napišite kartezično implementacijo kompleksnih števil, kjer ima vsako
   kompleksno število realno in imaginarno komponento.
  [*----------------------------------------------------------------------------*)

module Cartesian : COMPLEX = struct
  type t = { re : float; im : float }

  let eq x y = failwith "later"
  (* Dodajte manjkajoče! *)
end

(*----------------------------------------------------------------------------*
   Sedaj napišite še polarno implementacijo kompleksnih števil, kjer ima vsako
   kompleksno število radij in kot (angl. magnitude in argument). Priporočilo:
   Seštevanje je v polarnih koordinatah zahtevnejše, zato si ga pustite za konec
   (lahko tudi za konec stoletja).
  [*----------------------------------------------------------------------------*)

module Polar : COMPLEX = struct
  type t = { magn : float; arg : float }

  (* Pomožne funkcije za lažje življenje. *)
  let pi = 2. *. acos 0.
  let rad_of_deg deg = deg /. 180. *. pi
  let deg_of_rad rad = rad /. pi *. 180.
  let eq x y = failwith "later"
  (* Dodajte manjkajoče! *)
end
