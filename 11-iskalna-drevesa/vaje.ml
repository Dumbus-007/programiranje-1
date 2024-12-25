(* ========== Vaja 4: Iskalna Drevesa  ========== *)

(*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*]
   Ocaml omogoča enostavno delo z drevesi. Konstruiramo nov tip dreves, ki so
   bodisi prazna, bodisi pa vsebujejo podatek in imajo dve (morda prazni)
   poddrevesi. Na tej točki ne predpostavljamo ničesar drugega o obliki dreves.
  [*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*)

type 'a t = Prazno | Sestavljeno of 'a t * 'a * 'a t

(*----------------------------------------------------------------------------*]
   Definirajmo si testni primer za preizkušanje funkcij v nadaljevanju. Testni
   primer predstavlja spodaj narisano drevo, pomagamo pa si s pomožno funkcijo
   [leaf], ki iz podatka zgradi list.
            5
           / \
          2   7
         /   / \
        0   6   11
  [*----------------------------------------------------------------------------*)
let leaf : 'a -> 'a t = fun x -> Sestavljeno (Prazno, x, Prazno)

let test_tree =
  Sestavljeno
    (Sestavljeno (leaf 0, 2, Prazno), 5, Sestavljeno (leaf 6, 7, leaf 11))

(*----------------------------------------------------------------------------*]
   Funkcija [mirror] vrne prezrcaljeno drevo. Na primeru [test_tree] torej vrne
            5
           / \
          7   2
         / \   \
        11  6   0
   - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   # mirror test_tree ;;
   - : int tree =
   Node (Node (Node (Empty, 11, Empty), 7, Node (Empty, 6, Empty)), 5,
   Node (Empty, 2, Node (Empty, 0, Empty)))
  [*----------------------------------------------------------------------------*)
let rec mirror : 'a t -> 'a t =
 fun drevo ->
  match drevo with
  | Prazno -> Prazno
  | Sestavljeno (l, x, d) -> Sestavljeno (mirror d, x, mirror l)

(*----------------------------------------------------------------------------*]
   Funkcija [height] vrne višino oz. globino drevesa, funkcija [size] pa število
   vseh vozlišč drevesa.
   - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   # height test_tree;;
   - : int = 3
   # size test_tree;;
   - : int = 6
  [*----------------------------------------------------------------------------*)
let rec height : 'a t -> int =
 fun drevo ->
  match drevo with
  | Prazno -> 0
  | Sestavljeno (l, x, d) -> 1 + max (height l) (height d)

let rec size : 'a t -> int =
 fun drevo ->
  match drevo with Prazno -> 0 | Sestavljeno (l, x, d) -> 1 + size l + size d

(*----------------------------------------------------------------------------*]
   Funkcija [map_tree f tree] preslika drevo v novo drevo, ki vsebuje podatke
   drevesa [tree] preslikane s funkcijo [f].
   - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   # map_tree ((<)3) test_tree;;
   - : bool tree =
   Node (Node (Node (Empty, false, Empty), false, Empty), true,
   Node (Node (Empty, true, Empty), true, Node (Empty, true, Empty)))
  [*----------------------------------------------------------------------------*)
let rec map_tree f tree =
  match tree with
  | Prazno -> Prazno
  | Sestavljeno (l, x, d) -> Sestavljeno (map_tree f l, f x, map_tree f d)

(*----------------------------------------------------------------------------*]
   Funkcija [list_of_tree] pretvori drevo v seznam. Vrstni red podatkov v seznamu
   naj bo takšen, da v primeru binarnega iskalnega drevesa vrne urejen seznam.
   - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   # list_of_tree test_tree;;
   - : int list = [0; 2; 5; 6; 7; 11]
  [*----------------------------------------------------------------------------*)
let rec list_of_tree drevo =
  match drevo with
  | Prazno -> []
  | Sestavljeno (l, x, d) -> list_of_tree l @ [ x ] @ list_of_tree d

(*----------------------------------------------------------------------------*]
   Funkcija [is_bst] preveri ali je drevo binarno iskalno drevo (Binary Search
   Tree, na kratko BST). Predpostavite, da v drevesu ni ponovitev elementov,
   torej drevo npr. ni oblike Node( leaf 1, 1, leaf 2)). Prazno drevo je BST.
   - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   # is_bst test_tree;;
   - : bool = true
   # test_tree |> mirror |> is_bst;;
   - : bool = false
  [*----------------------------------------------------------------------------*)
let is_sorted lst = if lst = List.sort compare lst then true else false

let is_bst drevo =
  match drevo with
  | Prazno -> true
  | Sestavljeno (l, x, d) -> is_sorted (list_of_tree (Sestavljeno (l, x, d)))
(*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*]
   V nadaljevanju predpostavljamo, da imajo dvojiška drevesa strukturo BST.
  [*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*)

(*----------------------------------------------------------------------------*]
   Funkcija [insert] v iskalno drevo pravilno vstavi dani element. Funkcija
   [member] preveri ali je dani element v iskalnem drevesu.
   - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   # insert 2 (leaf 4);;
   - : int tree = Node (Node (Empty, 2, Empty), 4, Empty)
   # member 3 test_tree;;
   - : bool = false
  [*----------------------------------------------------------------------------*)
let rec member x tree =
  match tree with
  | Prazno -> false
  | Sestavljeno (l, y, d) when y > x -> member x l
  | Sestavljeno (l, y, d) when y < x -> member x d
  | _ -> true

let insert x tree =
  if member x tree then tree
  else
    match tree with
    | Prazno -> leaf x
    | Sestavljeno (l, y, d) -> failwith "todo"
(*----------------------------------------------------------------------------*]
   Funkcija [member2] ne privzame, da je drevo bst.

   Opomba: Premislte kolikšna je časovna zahtevnost funkcije [member] in kolikšna
   funkcije [member2] na drevesu z n vozlišči, ki ima globino log(n).
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*]
   Funkcija [succ] vrne naslednjika korena danega drevesa, če obstaja. Za drevo
   oblike [bst = Node(l, x, r)] vrne najmanjši element drevesa [bst], ki je večji
   od korena [x].
   Funkcija [pred] simetrično vrne največji element drevesa, ki je manjši od
   korena, če obstaja.
   - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   # succ test_tree;;
   - : int option = Some 6
   # pred (Node(Empty, 5, leaf 7));;
   - : int option = None
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*]
   Na predavanjih ste omenili dva načina brisanja elementov iz drevesa. Prvi
   uporablja [succ], drugi pa [pred]. Funkcija [delete x bst] iz drevesa [bst]
   izbriše element [x], če ta v drevesu obstaja. Za vajo lahko implementirate
   oba načina brisanja elementov.
   - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   # (*<< Za [delete] definiran s funkcijo [succ]. >>*)
   # delete 7 test_tree;;
   - : int tree =
   Node (Node (Node (Empty, 0, Empty), 2, Empty), 5,
   Node (Node (Empty, 6, Empty), 11, Empty))
  [*----------------------------------------------------------------------------*)

(*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*]
   SLOVARJI

   S pomočjo BST lahko (zadovoljivo) učinkovito definiramo slovarje. V praksi se
   slovarje definira s pomočjo hash tabel, ki so še učinkovitejše. V nadaljevanju
   pa predpostavimo, da so naši slovarji [dict] binarna iskalna drevesa, ki v
   vsakem vozlišču hranijo tako ključ kot tudi pripadajočo vrednost, in imajo BST
   strukturo glede na ključe. Ker slovar potrebuje parameter za tip ključa in tip
   vrednosti, ga parametriziramo kot [('key, 'value) dict].
  [*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*)

(*----------------------------------------------------------------------------*]
   Napišite testni primer [test_dict]:
        "b":1
        /    \
    "a":0  "d":2
           /
       "c":-2
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*]
   Funkcija [dict_get key dict] v slovarju poišče vrednost z ključem [key]. Ker
   slovar vrednosti morda ne vsebuje, vrne [option] tip.
   - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   # dict_get "banana" test_dict;;
   - : 'a option = None
   # dict_get "c" test_dict;;
   - : int option = Some (-2)
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*]
   Funkcija [print_dict] sprejme slovar s ključi tipa [string] in vrednostmi tipa
   [int] in v pravilnem vrstnem redu izpiše vrstice "ključ : vrednost" za vsa
   vozlišča slovarja.
   Namig: Uporabite funkciji [print_string] in [print_int]. Nize združujemo z
   operatorjem [^]. V tipu funkcije si oglejte, kako uporaba teh funkcij določi
   parametra za tip ključev in vrednosti v primerjavi s tipom [dict_get].
   - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   # print_dict test_dict;;
   a : 0
   b : 1
   c : -2
   d : 2
   - : unit = ()
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*]
   Funkcija [dict_insert key value dict] v slovar [dict] pod ključ [key] vstavi
   vrednost [value]. Če za nek ključ vrednost že obstaja, jo zamenja.
   - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   # dict_insert "1" 14 test_dict |> print_dict;;
   1 : 14
   a : 0
   b : 1
   c : -2
   d : 2
   - : unit = ()
   # dict_insert "c" 14 test_dict |> print_dict;;
   a : 0
   b : 1
   c : 14
   d : 2
   - : unit = ()
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*]
   Napišite primerno signaturo za slovarje [DICT] in naredite implementacijo
   modula z drevesi.

   Modul naj vsebuje prazen slovar [empty] in pa funkcije [get], [insert] in
   [print] (print naj ponovno deluje zgolj na [(string, int) t].
  [*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*]
   Funkcija [count (module Dict) list] prešteje in izpiše pojavitve posameznih
   elementov v seznamu [list] s pomočjo izbranega modula slovarjev.
   - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   # count (module Tree_dict) ["b"; "a"; "n"; "a"; "n"; "a"];;
   a : 3
   b : 1
   n : 2
   - : unit = ()
  [*----------------------------------------------------------------------------*)
