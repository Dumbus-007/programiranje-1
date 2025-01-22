(*----------------------------------------------------------------------------*
   # 4. domača naloga
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
   Pri tej nalogi boste napisali svoj simulator Turingovih strojev. Zaradi
   preprostosti bomo za abecedo vzeli kar znake tipa `char`, za prazni znak bomo
   izbrali presledek `' '`, stanja pa bomo predstavili z nizi. Za možne premike
   zafiksiramo tip `direction`:
  [*----------------------------------------------------------------------------*)

type direction = Left | Right
type state = string

(*----------------------------------------------------------------------------*
   ## Implementacija trakov
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
   Napišite modul `Tape`, ki implementira spodnjo signaturo, kjer je:

   - `t` tip v obe smeri neomejenih trakov in glavo na danem mestu;
   - `make`, ki naredi nov trak z znaki iz niza ter glavo na prvem znaku;
   - `print`, ki izpiše vsebino traku (brez presledkov na začetku in koncu) ter
   pod njim z `^` označi mesto glave;
   - `read`, ki vrne znak pod glavo;
   - `write`, ki pod glavo zapiše dani znak;
   - `move`, ki glavo premakne v dano smer.

   Zadnji dve funkciji naj vrneta nov trak, obstoječega pa naj pustita
   nespremenjenega.

   Ker je tip `t` abstrakten, si lahko privoščite poljubno implementacijo, zato
   poskrbite tako za učinkovitost kot za preglednost kode.
  [*----------------------------------------------------------------------------*)

module type TAPE = sig
  type t

  val make : string -> t
  val print : t -> unit
  val read : t -> char
  val move : direction -> t -> t
  val write : char -> t -> t
end

module Tape : TAPE = struct
  type t = { levo : char list; glava : char; desno : char list }

  let str_to_char_list s = List.init (String.length s) (String.get s)

  let make : string -> t =
   fun niz ->
    let sez = str_to_char_list niz in
    match sez with
    | [] -> { levo = []; glava = ' '; desno = [] }
    | x :: xs -> { levo = []; glava = x; desno = xs }

  let move : direction -> t -> t =
   fun smer { levo = xs; glava = a; desno = ys } ->
    match smer with
    | Left -> (
        match List.rev xs with
        | [] -> { levo = []; glava = ' '; desno = a :: ys }
        | x :: xs' -> { levo = List.rev xs'; glava = x; desno = a :: ys })
    | Right -> (
        match ys with
        | [] -> { levo = List.rev (a :: List.rev xs); glava = ' '; desno = [] }
        | y :: ys' ->
            { levo = List.rev (a :: List.rev xs); glava = y; desno = ys' })

  let read : t -> char = fun { levo = xs; glava = a; desno = ys } -> a

  let write : char -> t -> t =
   fun b { levo = xs; glava = a; desno = ys } ->
    { levo = xs; glava = b; desno = ys }

  let rec spucej_presledke sez =
    match sez with x :: xs when x = ' ' -> spucej_presledke xs | _ -> sez

  let print : t -> unit =
   fun { levo = xs; glava = a; desno = ys } ->
    let levi_str = String.of_seq (List.to_seq (spucej_presledke xs)) in
    let desni_str = String.of_seq (List.to_seq ys) in
    let za_printat = levi_str ^ String.make 1 a ^ desni_str in
    let pozicija = List.length (spucej_presledke xs) in
    Printf.printf "%s\n%s\n" za_printat (String.make pozicija ' ' ^ "^");
    flush stdout
end

let primer_trak =
  Tape.(
    make "ABCDE" |> move Left |> move Left |> move Right |> move Right
    |> move Right |> move Right |> write '!' |> print)

(*
AB!DE
  ^
*)
(* val primer_trak : unit = () *)

(*----------------------------------------------------------------------------*
   ## Implementacija Turingovih strojev
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
   Napišite modul `Machine`, ki implementira spodnjo signaturo, kjer je:

   - `t` tip Turingovih strojev;
   - `make`, ki naredi nov stroj z danim začetnim stanjem in seznamom preostalih
   stanj ter prazno prehodno funkcijo;
   - `initial`, ki vrne začetno stanje stroja;
   - `add_transition`, ki prehodno funkcijo razširi s prehodom $(q, a) \mapsto
   (q', a', d)$;
   - `step`, ki za dano stanje in trak izvede en korak stroja, če je to mogoče.

   Zadnji dve funkciji naj vrneta spremenjene vrednosti, obstoječe argumente pa
   naj pustita nespremenjene. Prav tako pri zadnjih dveh funkcijah lahko
   predpostavite, da ju bomo klicali le na poprej podanih stanjih.

   Tudi tu je tip `t` abstrakten, zato poskrbite za učinkovitost in preglednost
   kode.
  [*----------------------------------------------------------------------------*)
module type MNOZICA = sig
  type 'a t

  val vsebuje : 'a t -> 'a -> bool
  val prazna : 'a t
  val velikost : 'a t -> int
  val dodaj : 'a -> 'a t -> 'a t
  val razdeli : 'a t -> ('a t * 'a * 'a t) option
end

module MnozicaPrekPravilnoImplementiranihAVLDreves : MNOZICA = struct
  type 'a t = Prazno | Sestavljeno of int * 'a t * 'a * 'a t

  let rec vsebuje mn x =
    match mn with
    | Prazno -> false
    | Sestavljeno (_, l, y, d) when x = y -> true
    | Sestavljeno (_, l, y, d) when x < y -> vsebuje l x
    | Sestavljeno (_, l, y, d) when x > y -> vsebuje d x
    | _ -> assert false

  let prazna = Prazno

  let rec velikost = function
    | Prazno -> 0
    | Sestavljeno (_, l, _, d) -> 1 + velikost l + velikost d

  let visina drevo =
    match drevo with Prazno -> 0 | Sestavljeno (h, _, _, _) -> h

  let sestavljeno (l, x, d) =
    Sestavljeno (1 + max (visina l) (visina d), l, x, d)

  let zavrti_levo = function
    | Sestavljeno (_, l, x, Sestavljeno (_, dl, y, dd)) ->
        sestavljeno (sestavljeno (l, x, dl), y, dd)
    | _ -> failwith "Tega drevesa ne morem zavrteti"

  let zavrti_desno = function
    | Sestavljeno (_, Sestavljeno (_, ll, y, ld), x, d) ->
        sestavljeno (ll, y, sestavljeno (ld, x, d))
    | _ -> failwith "Tega drevesa ne morem zavrteti"

  let razlika = function
    | Prazno -> 0
    | Sestavljeno (_, l, _, d) -> visina l - visina d

  let uravnotezi drevo =
    match drevo with
    | Sestavljeno (_, l, x, d) when razlika drevo = 2 && razlika l = 1 ->
        zavrti_desno drevo
    | Sestavljeno (_, l, x, d) when razlika drevo = 2 ->
        sestavljeno (zavrti_levo l, x, d) |> zavrti_desno
    | Sestavljeno (_, l, x, d) when razlika drevo = -2 && razlika d = -1 ->
        zavrti_levo drevo
    | Sestavljeno (_, l, x, d) when razlika drevo = -2 ->
        sestavljeno (l, x, zavrti_desno d) |> zavrti_levo
    | _ -> drevo

  let rec isci x drevo =
    match drevo with
    | Prazno -> false
    | Sestavljeno (_, l, vrednost, d) ->
        if x < vrednost then isci x l
        else if x > vrednost then isci x d
        else true

  let rec dodaj x drevo =
    match drevo with
    | Prazno -> Sestavljeno (1, Prazno, x, Prazno)
    | Sestavljeno (h, l, vrednost, d) ->
        if x < vrednost then sestavljeno (dodaj x l, vrednost, d) |> uravnotezi
        else if x > vrednost then
          sestavljeno (l, vrednost, dodaj x d) |> uravnotezi
        else drevo

  let je_prazno = function Prazno -> true | _ -> false

  let razdeli = function
    | Sestavljeno (_, l, x, d) -> Some (l, x, d)
    | Prazno -> None
end

module type MACHINE = sig
  type t

  val make : state -> state list -> t
  val initial : t -> state
  val add_transition : state -> char -> state -> char -> direction -> t -> t
  val step : t -> state -> Tape.t -> (state * Tape.t) option
end

module Machine : MACHINE = struct
  type transition_key = state * char
  type transition_value = state * char * direction

  (* AVL drevo za prehode *)
  module Transitions = struct
    include MnozicaPrekPravilnoImplementiranihAVLDreves

    (* Funkcija za primerjavo ključev (state * char) *)
    let compare_transition (q1, a1) (q2, a2) =
      match compare q1 q2 with 0 -> compare a1 a2 | cmp -> cmp
  end

  (* Tip za Turingov stroj *)
  type t = {
    zacetno_stanje : state;
    stanja : state list;
    prehodi : (transition_key * transition_value) Transitions.t;
  }

  (* Inicializacija stroja *)
  let make zacetek stanja =
    { zacetno_stanje = zacetek; stanja; prehodi = Transitions.prazna }

  (* Vrne začetno stanje stroja *)
  let initial m = m.zacetno_stanje

  (* Dodaj prehod v stroj *)
  let add_transition q a q' a' d m =
    let nov_prehod = ((q, a), (q', a', d)) in
    let novi_prehodi = Transitions.dodaj nov_prehod m.prehodi in
    { m with prehodi = novi_prehodi }

  (* Poišči prehod *)
  let rec find_transition key prehodi =
    match Transitions.razdeli prehodi with
    | None -> None
    | Some (l, (k, v), d) ->
        if key < k then find_transition key l
        else if key > k then find_transition key d
        else Some v

  (* Izvedi korak stroja *)
  let step m stanje trak =
    match find_transition (stanje, Tape.read trak) m.prehodi with
    | None -> None (* Ni prehoda za trenutno stanje in znak *)
    | Some (novo_stanje, nov_znak, smer) ->
        let nov_trak = Tape.write nov_znak trak |> Tape.move smer in
        Some (novo_stanje, nov_trak)
end

(*----------------------------------------------------------------------------*
   Primer stroja "Binary Increment" na <http://turingmachine.io> lahko
   implementiramo kot:
  [*----------------------------------------------------------------------------*)

let binary_increment =
  Machine.(
    make "right" [ "carry"; "done" ]
    |> add_transition "right" '1' "right" '1' Right
    |> add_transition "right" '0' "right" '0' Right
    |> add_transition "right" ' ' "carry" ' ' Left
    |> add_transition "carry" '1' "carry" '0' Left
    |> add_transition "carry" '0' "done" '1' Left
    |> add_transition "carry" ' ' "done" '1' Left)

(* val binary_increment : Machine.t = <abstr> *)

(*----------------------------------------------------------------------------*
   Zapišite funkciji `slow_run` in `speed_run` tipa `Machine.t -> str -> unit`, ki
   simulirata Turingov stroj na traku, na katerem je na začetku zapisan dani niz.
   Prva naj izpiše trakove in stanja pri vseh vmesnih korakih, druga pa naj izpiše
   le končni trak. Slednjo bomo uporabljali tudi pri meritvi učinkovitosti
   izvajanja.
  [*----------------------------------------------------------------------------*)

let slow_run : Machine.t -> string -> unit =
 fun m niz ->
  let rec pomozna stanje trak =
    Tape.print trak;
    Printf.printf "%s\n" stanje;
    match Machine.step m stanje trak with
    | Some (novo_st, nov_trak) -> pomozna novo_st nov_trak
    | None -> ()
  in
  let trak = Tape.make niz in
  pomozna (Machine.initial m) trak

let slow_run' : Machine.t -> string -> unit =
 fun m niz ->
  let rec pomozna stanje trak =
    match Machine.step m stanje trak with
    | Some (novo_st, nov_trak) ->
        Tape.print trak;
        (* Print the tape *)
        Printf.printf "%s\n" stanje;
        (* Print the current state *)
        pomozna novo_st nov_trak (* Continue with the next step *)
    | None ->
        (* When no transition exists (machine halts) *)
        Tape.print trak;
        (* Print the final tape *)
        Printf.printf "%s\n" stanje
    (* Print the final state *)
  in
  let trak = Tape.make niz in
  pomozna (Machine.initial m) trak

let primer_slow_run = slow_run binary_increment "1011"
(*
1011
^
right
1011
  ^
right
1011
  ^
right
1011
    ^
right
1011
    ^
right
1011
    ^
carry
1010
  ^
carry
1000
  ^
carry
1100
^
done
*)
(* val primer_slow_run : unit = () *)

let speed_run : Machine.t -> string -> unit =
 fun m niz ->
  let rec pomozna stanje trak =
    match Machine.step m stanje trak with
    | None -> Tape.print trak
    | Some (novo_st, nov_trak) -> pomozna novo_st nov_trak
  in
  let trak = Tape.make niz in
  pomozna (Machine.initial m) trak

let primer_speed_run = speed_run binary_increment "1011"

(*
1100
^
*)
(* val primer_speed_run : unit = () *)

(*----------------------------------------------------------------------------*
   ## Krajši zapis
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
   Ko definiramo Turingov stroj, prehode običajno združujemo najprej po stanjih,
   nato pa še po znakih. Prav tako pri dosti prehodih samo premikamo glavo, trak
   in stanje pa pustimo pri miru. Zapišite funkcije:

   - `for_state`
   - `for_character`
   - `for_characters`
   - `move`
   - `switch_and_move`
   - `write_and_move`
   - `write_switch_and_move`

   s katerimi bi lahko zgornji primer na krajše zapisali kot spodaj.
   Implementacijo in tipe ugotovite sami.
  [*----------------------------------------------------------------------------*)
let for_state stanje operacije m =
  List.fold_left (fun acc op -> op stanje acc) m operacije

let for_character (znak : char)
    (akcija : state -> char -> Machine.t -> Machine.t) (trenutno_stanje : state)
    (m : Machine.t) =
  akcija trenutno_stanje znak m

let for_characters (znaki : string)
    (akcija : state -> char -> Machine.t -> Machine.t) (trenutno_stanje : state)
    (m : Machine.t) =
  String.fold_left (fun acc znak -> akcija trenutno_stanje znak acc) m znaki

let move (smer : direction) (trenutno_stanje : state) (znak : char)
    (m : Machine.t) =
  Machine.add_transition trenutno_stanje znak trenutno_stanje znak smer m

let switch_and_move (novo_stanje : state) (smer : direction)
    (trenutno_stanje : state) (znak : char) (m : Machine.t) =
  Machine.add_transition trenutno_stanje znak novo_stanje znak smer m

let write_switch_and_move (nov_znak : char) (novo_stanje : state)
    (smer : direction) (trenutno_stanje : state) (znak : char) (m : Machine.t) =
  Machine.add_transition trenutno_stanje znak novo_stanje nov_znak smer m

let busy_beaver5 =
  Machine.(
    make "A" [ "B"; "C"; "D"; "E" ]
    |> add_transition "A" ' ' "B" '1' Right
    |> add_transition "A" '1' "C" '1' Left
    |> add_transition "B" ' ' "C" '1' Right
    |> add_transition "B" '1' "B" '1' Right
    |> add_transition "C" ' ' "D" '1' Right
    |> add_transition "C" '1' "E" ' ' Left
    |> add_transition "D" ' ' "A" '1' Left
    |> add_transition "D" '1' "D" '1' Left
    |> add_transition "E" '1' "A" ' ' Left)
(* let binary_increment' =
   Machine.make "right" ["carry"; "done"]
   |> for_state "right" [
     for_characters "01" @@ move Right;
     for_character ' ' @@ switch_and_move "carry" Left
   ]
   |> for_state "carry" [
     for_character '1' @@ write_and_move '0' Left;
     for_characters "0 " @@ write_switch_and_move '1' "done" Left
   ] *)
(* val binary_increment' : Machine.t = <abstr> *)

(*----------------------------------------------------------------------------*
   ## Primeri Turingovih strojev
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
   Pri tej nalogi boste sestavljali stroje, ki bodo iz začetnega niza na traku na
   različne načine izračunali nov niz. Pri tem lahko predpostavite, da je začetni
   niz sestavljen iz ničel in enic, preostanek traku pa je prazen. Na koncu
   izvajanja naj bo glava na začetku novega niza, z izjemo tega niza pa naj bo
   trak prazen. Ni pa treba, da se izračunani niz začne na istem mestu na traku,
   kot se je začel prvotni niz.
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
   ### Obračanje niza
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
   Sestavite Turingov stroj, ki začetni niz obrne na glavo.
  [*----------------------------------------------------------------------------*)

let reverse = ()
let primer_reverse = speed_run reverse "0000111001"
(*
   1001110000
   ^
*)
(* val primer_reverse : unit = () *)

(*----------------------------------------------------------------------------*
   ### Podvajanje niza
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
   Sestavite Turingov stroj, ki podvoji začetni niz.
  [*----------------------------------------------------------------------------*)

let duplicate = ()
let primer_duplicate = speed_run duplicate "010011"
(*
   001100001111
   ^
*)
(* val primer_duplicate : unit = () *)

(*----------------------------------------------------------------------------*
   ### Eniški zapis
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
   Sestavite Turingov stroj, ki na začetku na traku sprejme število $n$, zapisano
   v dvojiškem zapisu, na koncu pa naj bo na traku zapisanih natanko $n$ enic.
  [*----------------------------------------------------------------------------*)

let to_unary = ()
let primer_to_unary = speed_run to_unary "1010"
(*
   1111111111
   ^
*)
(* val primer_to_unary : unit = () *)

(*----------------------------------------------------------------------------*
   ### Dvojiški zapis
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
   Sestavite ravno obratni Turingov stroj, torej tak, ki na začetku na traku
   sprejme število $n$ enic, na koncu pa naj bo na traku zapisano število $n$ v
   dvojiškem zapisu.
  [*----------------------------------------------------------------------------*)

let to_binary = ()
let primer_to_binary = speed_run to_binary (String.make 42 '1')
(*
   101010
   ^
*)
(* val primer_to_binary : unit = () *)
