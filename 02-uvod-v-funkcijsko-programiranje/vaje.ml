<<<<<<< HEAD
(* ========== Vaja 2: Uvod v funkcijsko programiranje  ========== *)

(*----------------------------------------------------------------------------*]
  Vektorje predstavimo kot seznam števil s plavajočo vejico.
  [*----------------------------------------------------------------------------*)

type vector = float list

(*----------------------------------------------------------------------------*]
  Definirajte enotske vektorje `i`, `j` in `k` v treh dimenzijah.
  [*----------------------------------------------------------------------------*)
let i = [ 1.0; 0.0; 0.0 ]
let j = [ 0.0; 1.0; 0.0 ]
let k = [ 0.0; 0.0; 1.0 ]
(*----------------------------------------------------------------------------*]
  Napišite funkcijo `razteg : float -> vector -> vector`, ki vektor,
  predstavljen s seznamom števil s plavajočo vejico, pomnoži z danim skalarjem.
  [*----------------------------------------------------------------------------*)

let pomnozi x y = x *. y
let razteg a vec = List.map (pomnozi a) vec

(*----------------------------------------------------------------------------*]
  Napišite funkcijo `sestej : vector -> vector -> vector`, ki vrne vsoto dveh
  vektorjev.
  [*----------------------------------------------------------------------------*)

let sestej vec1 vec2 = List.map2 ( +. ) vec1 vec2

(*----------------------------------------------------------------------------*]
  Napišite funkcijo `skalarni_produkt : vector -> vector -> float`, ki izračuna
  skalarni produkt dveh vektorjev
  [*----------------------------------------------------------------------------*)
let skalarni_produkt vec1 vec2 =
  let zmnozki = List.map2 pomnozi vec1 vec2 in
  List.fold_left ( +. ) 0.0 zmnozki

(*----------------------------------------------------------------------------*]
  Napišite funkcijo `norma : vector -> float`, ki vrne evklidsko normo vektorja.
  [*----------------------------------------------------------------------------*)

let norma vec = skalarni_produkt vec vec ** 0.5

(*----------------------------------------------------------------------------*]
  Napišite funkcijo `projeciraj : vector -> vector -> vector`, ki izračuna
  projekcijo prvega vektorja na drugega.
  [*----------------------------------------------------------------------------*)

let projeciraj vec1 vec2 =
  let skalar = skalarni_produkt vec1 vec2 /. norma vec2 in
  razteg skalar vec2

(*----------------------------------------------------------------------------*]
  Napišite funkcijo `ovij : string -> string -> string`, ki sprejme ime HTML
  oznake in vsebino ter vrne niz, ki predstavlja ustrezno HTML oznako.

  Primer:
  `ovij "h1" "Hello, world!"`

  [*----------------------------------------------------------------------------*)

let ovij znacka tekst = "<" ^ znacka ^ ">" ^ tekst ^ "<" ^ znacka ^ ">"

(*----------------------------------------------------------------------------*]
  Napišite funkcijo `zamakni : int -> string -> string`, ki sprejme število
  presledkov in niz ter vrne niz, v katerem je vsaka vrstica zamaknjena za ustrezno število presledkov.

  Primer:
  `zamakni 4 "Hello, world!"`

  [*----------------------------------------------------------------------------*)
=======
(*----------------------------------------------------------------------------*
 # Uvod v funkcijsko programiranje
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 ## Vektorji
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `razteg : float -> float list -> float list`, ki vektor,
 predstavljen s seznamom števil s plavajočo vejico, pomnoži z danim skalarjem.
[*----------------------------------------------------------------------------*)

let razteg _ _ = ()

let primer_vektorji_1 = razteg 2.0 [1.0; 2.0; 3.0]
(* val primer_vektorji_1 : float list = [2.; 4.; 6.] *)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `sestej : float list -> float list -> float list`, ki vrne
 vsoto dveh vektorjev.
[*----------------------------------------------------------------------------*)

let sestej _ _ = ()

let primer_vektorji_2 = sestej [1.0; 2.0; 3.0] [4.0; 5.0; 6.0]
(* val primer_vektorji_2 : float list = [5.; 7.; 9.] *)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `skalarni_produkt : float list -> float list -> float`, ki
 izračuna skalarni produkt dveh vektorjev. Pri tem si lahko pomagate s funkcijo
 `vsota_seznama : float list -> float`, definirano prek funkcije
 `List.fold_left`, ki jo bomo spoznali kasneje:
[*----------------------------------------------------------------------------*)

let vsota_seznama = List.fold_left (+.) 0.

let skalarni_produkt _ _ = ()

let primer_vektorji_3 = skalarni_produkt [1.0; 2.0; 3.0] [4.0; 5.0; 6.0]
(* val primer_vektorji_3 : float = 32. *)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `norma : float list -> float`, ki vrne evklidsko normo
 vektorja.
[*----------------------------------------------------------------------------*)

let norma _ = ()

let primer_vektorji_4 = norma [3.0; 4.0]
(* val primer_vektorji_4 : float = 5. *)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `vmesni_kot : float list -> float list -> float`, ki izračuna
 kot med dvema vektorjema v radianih.
[*----------------------------------------------------------------------------*)

let vmesni_kot _ _ = ()

let primer_vektorji_5 = vmesni_kot [1.0; 0.0] [0.0; 1.0]
(* val primer_vektorji_5 : float = 1.57079632679489656 *)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `normirani : float list -> float list`, ki normira dani
 vektor.
[*----------------------------------------------------------------------------*)

let normirani _ = ()

let primer_vektorji_6 = normirani [3.0; 4.0]
(* val primer_vektorji_6 : float list = [0.600000000000000089; 0.8] *)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `projeciraj : float list -> float list -> float list`, ki
 izračuna projekcijo prvega vektorja na drugega.
[*----------------------------------------------------------------------------*)
>>>>>>> a4d358dfc8a8366ab7a4b866b1fe4c013407c2bf

let projekcija _ _ = ()

<<<<<<< HEAD
(*----------------------------------------------------------------------------*]
  Napišite funkcijo `ul : string list -> string`, ki sprejme seznam nizov in vrne
  niz, ki predstavlja ustrezno zamaknjen neurejeni seznam v HTML-ju:

  Primer:
  `ul ["ananas"; "banana"; "čokolada"]`

  [*----------------------------------------------------------------------------*)

let rec ul = ()

(*----------------------------------------------------------------------------*]
  Napišite funkcijo `razdeli_vrstico : string -> string * string`, ki sprejme niz,
  ki vsebuje vejico, loči na del pred in del za njo.

  Primer:
  `razdeli_vrstico "mleko, 2"`

  [*----------------------------------------------------------------------------*)
=======
let primer_vektorji_7 = projekcija [3.0; 4.0] [1.0; 0.0]
(* val primer_vektorji_7 : float list = [3.; 0.] *)

(*----------------------------------------------------------------------------*
 ## Generiranje HTML-ja
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `ovij : string -> string -> string`, ki sprejme ime HTML
 oznake in vsebino ter vrne niz, ki predstavlja ustrezno HTML oznako.
[*----------------------------------------------------------------------------*)
>>>>>>> a4d358dfc8a8366ab7a4b866b1fe4c013407c2bf

let ovij _ _ = ()

<<<<<<< HEAD
(*----------------------------------------------------------------------------*]
  Napišite funkcijo `pretvori_v_seznam_parov : string -> (string * string) list`,
  ki sprejme večvrstični niz, kjer je vsaka vrstica niz oblike
  "izdelek, vrednost", in vrne seznam ustreznih parov.

  Primer:
  `pretvori_v_seznam_parov "mleko, 2\nkruh, 1\njabolko, 5"`

  [*----------------------------------------------------------------------------*)
=======
let primer_html_1 = ovij "h1" "Hello, world!"
(* val primer_html_1 : string = "<h1>Hello, world!</h1>" *)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `zamakni : int -> string -> string`, ki sprejme število
 presledkov in niz ter vrne niz, v katerem je vsaka vrstica zamaknjena za
 ustrezno število presledkov.
[*----------------------------------------------------------------------------*)
>>>>>>> a4d358dfc8a8366ab7a4b866b1fe4c013407c2bf

let zamakni _ _ = ()

<<<<<<< HEAD
(*----------------------------------------------------------------------------*]
  Napišite funkcijo `pretvori_druge_komponente : ('a -> 'b) -> (string * 'a) list -> (string * 'b) list`,
  ki dano funkcijo uporabi na vseh drugih komponentah elementov seznama.

  Primer:
  ```ml
  let seznam = [("ata", "mama"); ("teta", "stric")] in
  pretvori_druge_komponente String.length seznam
  ```

  [*----------------------------------------------------------------------------*)
=======
let primer_html_2 = zamakni 4 "Hello,\nworld!"
(* val primer_html_2 : string = "    Hello,\n    world!" *)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `ul : string list -> string`, ki sprejme seznam nizov in vrne
 niz, ki predstavlja ustrezno zamaknjen neurejeni seznam v HTML-ju:
[*----------------------------------------------------------------------------*)
>>>>>>> a4d358dfc8a8366ab7a4b866b1fe4c013407c2bf

let ul _ = ()

<<<<<<< HEAD
(*----------------------------------------------------------------------------*]
  Napišite funkcijo `izracunaj_skupni_znesek : string -> string -> float`, ki
  sprejme večvrstična niza nakupovalnega seznama in cenika in izračuna skupni
  znesek nakupa.

  Primer:
  ```ml
  let nakupovalni_seznam = "mleko, 2\njabolka, 5"
  and cenik = "jabolka, 0.5\nkruh, 2\nmleko, 1.5" in
  izracunaj_skupni_znesek cenik nakupovalni_seznam
  ```

  [*----------------------------------------------------------------------------*)
=======
let primer_html_3 = ul ["ananas"; "banana"; "čokolada"]
(* val primer_html_3 : string =
  "<ul>\n  <li>ananas</li>\n  <li>banana</li>\n  <li>čokolada</li>\n</ul>" *)

(*----------------------------------------------------------------------------*
 ## Nakupovalni seznam
[*----------------------------------------------------------------------------*)
>>>>>>> a4d358dfc8a8366ab7a4b866b1fe4c013407c2bf

(*----------------------------------------------------------------------------*
 Napišite funkcijo `razdeli_vrstico : string -> string * string`, ki sprejme
 niz, ki vsebuje vejico, loči na del pred in del za njo.
[*----------------------------------------------------------------------------*)

let razdeli_vrstico _ = ()

let primer_seznam_1 = razdeli_vrstico "mleko, 2"
(* val primer_seznam_1 : string * string = ("mleko", "2") *)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `pretvori_v_seznam_parov : string -> (string * string) list`,
 ki sprejme večvrstični niz, kjer je vsaka vrstica niz oblike `"izdelek,
 vrednost"`, in vrne seznam ustreznih parov.
[*----------------------------------------------------------------------------*)

let pretvori_v_seznam_parov _ = ()

let primer_seznam_2 = pretvori_v_seznam_parov "mleko, 2\nkruh, 1\njabolko, 5"
(* val primer_seznam_2 : (string * string) list =
  [("mleko", "2"); ("kruh", "1"); ("jabolko", "5")] *)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `pretvori_druge_komponente : ('a -> 'b) -> (string * 'a) list
 -> (string * 'b) list`, ki dano funkcijo uporabi na vseh drugih komponentah
 elementov seznama.
[*----------------------------------------------------------------------------*)

let pretvori_druge_komponente _ _ = ()

let primer_seznam_3 =
  let seznam = [("ata", "mama"); ("teta", "stric")] in
  pretvori_druge_komponente String.length seznam
(* val primer_seznam_3 : (string * int) list = [("ata", 4); ("teta", 5)] *)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `izracunaj_skupni_znesek : string -> string -> float`, ki
 sprejme večvrstična niza nakupovalnega seznama in cenika in izračuna skupni
 znesek nakupa.
[*----------------------------------------------------------------------------*)

let izracunaj_skupni_znesek _ _ = ()

let primer_seznam_4 = 
  let nakupovalni_seznam = "mleko, 2\njabolka, 5"
  and cenik = "jabolka, 0.5\nkruh, 2\nmleko, 1.5" in
  izracunaj_skupni_znesek cenik nakupovalni_seznam
(* val primer_seznam_4 : float = 5.5 *)
