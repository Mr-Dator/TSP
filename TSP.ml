#load "graphics.cma";;(*Librairie pour la fenêtre Graphique*)
open Graphics;;
Random.self_init;;

let t = 790;;
let tbis = float_of_int t;;

let nouveauGraphe n =
	let f i = ((Random.float 1.,Random.float 1.),[]) in
	Array.init n f;;
List.iter;;
let sontAdjacents g x y = 
	let rec aux t x = match t with
	[] -> false
	|a::q -> if a=x then true else aux q x 
	in
	let v,l = g.(y) in aux l x;;

let ajouterArete g x y =
	let t = Array.length g in
	if x >= t || y>=t then failwith "Sommet absent"
	else if sontAdjacents g x y then failwith "Sommet déjà adjacents"
	else
	g.(x) <- (fst g.(x),y::snd g.(x)); 
	g.(y) <- (fst g.(y),x::snd g.(y));;

let supprimerArete g x y =
	let rec aux t x = match t with
		[] ->[]
		|a::q -> if x=a then q else a::aux q x 
	in
	if sontAdjacents g x y then 
	begin 
	g.(x) <- fst g.(x), aux (snd g.(x)) y; 
	g.(y) <- fst g.(y), aux (snd g.(y)) x 
	end 
	else failwith"Il n'y pas d'arete a supprimer";;

let existe g x = x < Array.length g;;

let voisins g x = if existe g x then snd g.(x) else failwith "Sommet absent";;

let valeurSommet g x = if existe g x then fst g.(x) else failwith"Sommet absent";;

let changerValeur g x v = if existe g x then g.(x) <- v,snd g.(x);;

let distance g x y =
	let u,v = valeurSommet g x in
	let y,z = valeurSommet g y in
	sqrt((u-.y)*.(u-.y) +. (v-.z)*.(v-.z));;

let rec longueur g trajet = match trajet with
	[] -> 0.
	|x::y::l -> (distance g x y) +. longueur g (y::l)
	|x::l -> 0.;;

let drawPath g trajet= if trajet = [] then () else

	let randomColor ()= 
		let r,g,b = Random.int 256, Random.int 256, Random.int 256 in
		rgb r g b in
	
	let rec drawTrajet l = match l with
		[] -> ()
		|s::r -> (*set_color (randomColor()); *)
					let x,y = int_of_float (tbis*.fst (fst(g.(s)))), int_of_float (tbis*.snd (fst(g.(s)))) in
					lineto x y;
					set_color(black);
					draw_circle x y 4; print_string;
					drawTrajet r in
	let d::r = trajet in 
	moveto (int_of_float (tbis*.fst (fst(g.(d))))) (int_of_float (tbis*.snd (fst(g.(d)))));
	drawTrajet trajet;;

let rec printListe l = match l with
	[] -> ()
	|a::q -> print_newline(); print_float a; printListe q;;

let rec drawTrajets g l = match l with
	[] -> ()
	|t::q -> drawPath g t; drawTrajets g q;;

print_string "Initialisation graphe";
print_newline();;



let rec listeFonctions g l = match l with (*Renvoie pour un graphe g la liste des trajets calculés par chaque algorithme de la liste*)
	[] -> []
	|f::h -> (f g)::(listeFonctions g h) ;;

let rec fSurListe f l = match l with (*Renvoie pour une fonction f la liste des images par f*)
	[] -> []
	|t::r -> (f t)::fSurListe f r;;

let rec isInListe v l = match l with
	[] -> false
	|s::q -> if s = v then true else isInListe v q;;


let rec permutations l = 
	let rec aux a p debut =
	(*insère a dans chaque position de p puis ajoute debut en tête*)
		match p with
			[] -> [debut@[a]]
			|x::r -> (debut@(a::p))::(aux a r (debut@[x]))
	in
	let rec aux2 a lp  =
	(* insère a dans chaque position de chaque liste de lp*)
		match lp with
			[] -> []
			|p::r -> (aux a p [])@(aux2 a r)
	in
	match l with
		[] -> [[]]
		|a::q -> aux2 a (permutations q);;

let bruteForce g = 

	let n = Array.length g in 
	let trajets = permutations (List.init n (fun i -> i)) in 
	
	let rec findMin l m n k = match l with 
		[] -> n
		|a::p -> if a < m then findMin p a (k+1) (k+1) else findMin p m n (k+1)
		in
	let rec nth l n k = match l with
		[] -> failwith "L'élément n'existe pas"
		|a::p -> if n = k then a else nth  p n (k+1)
		in
	let distances = List.init (List.length trajets) (fun i -> longueur g (nth trajets i 0)) in
	let m = findMin distances (2.*.float_of_int n) 0 0 in 
	nth trajets m 1(*, trajets, distances, m;*);;
	

	
let listeAlgo = [bruteForce];;

let main g = 
	let trajets = listeFonctions g listeAlgo in
	let rec calculDistances l g = match l with
		[] -> []
		|t::r -> (longueur g t)::calculDistances r g
		in
	calculDistances trajets g, trajets;;

(*PARAMETRAGE DU GRAPHE*)


let n = 7;;
let graphe = nouveauGraphe n;;
let disMatrix = Array.make_matrix n n 0.;;
for i = 0 to n-1 do
	for j = 0 to i do
		let d = distance graphe i j in
		disMatrix.(i).(j) <- d;
		disMatrix.(j).(i) <- d;
		done;
	done;;

	

(*let distances, trajets = main graphe in 
	printListe distances; drawTrajets graphe trajets;;*)
	
(*let traj = bruteForce graphe;;*)


let findMin t = 
	let n = Array.length t in
	let m = ref infinity in
	for k = 0 to n-1 do
		if t.(k) < !m then m := t.(k) else ()
		done;
	!m;;



let primApprox (n,graphe) =
	let g = graphe in 
	let rec insertFile u k file = match file with
		[] -> [(u, k)]
		|(v,l)::fileBis -> if k < l then (u, k)::file else (v,l):: insertFile u k fileBis in
	let rec isEmptyFile file = match file with
		[] -> true
		|_ -> false in
	let rec extraitFile file = match file with
		[] -> failwith "File vide"
		|(u,k)::fileBis -> (u,k) in
	let rec deleteFile u file = match file with
		[] -> failwith "File vide"
		|(v,k)::fileBis -> if u = v then fileBis else (v,k):: deleteFile u fileBis in
	let rec isInFile u file = match file with
		[] -> false,-1.
		|(v,k)::fileBis -> if u = v then true,k else isInFile u fileBis in
	let n = Array.length g in
	let file = ref [] in
	let predecesseur = Array.make n (-1) in
	predecesseur.(0) <- 0;
	for u = 1 to n-1 do
		file := insertFile u infinity !file;
		done;
	file:= insertFile 0 0. !file;
	while not (isEmptyFile !file) do
		let u,v = extraitFile !file in
		file := deleteFile u !file;
		for i = 0 to n-1 do
			let b,k = isInFile i !file in
			let d = distance g i u in
			if b && d < k then
				begin predecesseur.(i) <- u;
						file := deleteFile i !file;
						file := insertFile i d !file; end else()
			done;
		done;
	
	(*let compareCouples (p,s) (q,t) = match p,q with
		0,_ -> -1
		|_,0 -> 1
		|_,_ -> p-q in

	let predecesseurTri = Array.init n (fun i -> predecesseur.(i),i) in
	Array.sort compareCouples predecesseurTri;*)
	
	let calcSucc pred =
		let succ = Array.make n [] in
		for i = 0 to n - 1 do
			let j = pred.(i) in
			succ.(j) <- i :: succ.(j);(* Ajouter i à la liste des successeurs de j *)
			done;
		succ in
		
	let successeurs = calcSucc predecesseur in
	let trajet = ref [] in
	
	let dsfArbre succ =
		let visited = Array.make n false in
		let rec dfs i =
			visited.(i) <- true;
			trajet:= i::!trajet;
			List.iter (fun j -> if not visited.(j) then dfs j) succ.(i);
			in
			dfs 0 
	in dsfArbre successeurs;
	!trajet
	;;

let primApproxTree (n,graphe) =
	let g = graphe in 
	let rec insertFile u k file = match file with
		[] -> [(u, k)]
		|(v,l)::fileBis -> if k < l then (u, k)::file else (v,l):: insertFile u k fileBis in
	let rec isEmptyFile file = match file with
		[] -> true
		|_ -> false in
	let rec extraitFile file = match file with
		[] -> failwith "File vide"
		|(u,k)::fileBis -> (u,k) in
	let rec deleteFile u file = match file with
		[] -> failwith "File vide"
		|(v,k)::fileBis -> if u = v then fileBis else (v,k):: deleteFile u fileBis in
	let rec isInFile u file = match file with
		[] -> false,-1.
		|(v,k)::fileBis -> if u = v then true,k else isInFile u fileBis in
	let n = Array.length g in
	let file = ref [] in
	let predecesseur = Array.make n (-1) in
	predecesseur.(0) <- 0;
	for u = 1 to n-1 do
		file := insertFile u infinity !file;
		done;
	file:= insertFile 0 0. !file;
	while not (isEmptyFile !file) do
		let u,v = extraitFile !file in
		file := deleteFile u !file;
		for i = 0 to n-1 do
			let b,k = isInFile i !file in
			let d = distance g i u in
			if b && d < k then
				begin predecesseur.(i) <- u;
						file := deleteFile i !file;
						file := insertFile i d !file; end else()
			done;
		done;
	
	(*let compareCouples (p,s) (q,t) = match p,q with
		0,_ -> -1
		|_,0 -> 1
		|_,_ -> p-q in

	let predecesseurTri = Array.init n (fun i -> predecesseur.(i),i) in
	Array.sort compareCouples predecesseurTri;*)
	
	let calcSucc pred =
		let succ = Array.make n [] in
		for i = 0 to n - 1 do
			let j = pred.(i) in
			succ.(j) <- i :: succ.(j);(* Ajouter i à la liste des successeurs de j *)
			done;
		succ in
		
	let successeurs = calcSucc predecesseur in
	let trajet = ref [] in
	
	let dsfArbre succ =
		let visited = Array.make n false in
		let rec dfs i =
			visited.(i) <- true;
			trajet:= i::!trajet;
			List.iter (fun j -> if not visited.(j) then dfs j) succ.(i);
			in
			dfs 0 
	in dsfArbre successeurs;
	predecesseur
	;;

let drawTree pred =
	let n = Array.length pred in
	set_color black;
	for k = 0 to n-1 do
		let x,y = int_of_float (tbis*.fst (fst(graphe.(k)))), int_of_float (tbis*.snd (fst(graphe.(k)))) in
		let a,b= int_of_float (tbis*.fst (fst(graphe.(pred.(k))))), int_of_float (tbis*.snd (fst(graphe.(pred.(k))))) in
		moveto x y;
		draw_circle x y 4;
		lineto a b;
	done;
	;;


let antApprox (n,graphe) = 
	let nb = 80 in
	let duree= 25 in
	let pheromones = Array.make_matrix n n 1.0 in
	let probasMat = Array.make_matrix n n 0. in
	let ants = Array.init nb (fun i -> (ref [],ref 0.)) in
	let alpha = 0.9 in (*importance des pheromones*)
	let beta = 7.5 in (*importance des distances*)
	let rho = 0.00 in (*facteur de dissipation*)
	
	let actualiseProbas () = 
		for i = 0 to n-1 do
			for j = 0 to n-1 do
				let c = ref 0. in
				for k = 0 to n-1 do
					if k != i then c:= !c +. ((pheromones.(i).(k)**alpha) /. (float_of_int n *. distance graphe i k)**beta);
				done;
				if i!=j then probasMat.(i).(j) <- ((pheromones.(i).(j)**alpha) /. ((float_of_int n *. distance graphe i j)**beta))  /. (!c);
			done;
		done;
		in
	actualiseProbas ();
	
	let rec somme l = match l with
			[] -> 0.
			|a::p -> a +. somme p
			in
	
	let rec normalise l s = match l with
			[] -> []
			|a::p -> (a/.s)::normalise p s
			in
	
	let transition u ant=
		let antTraj,b = ant in
		let voisins = ref [] in
		let probas = ref [] in
		for k = 0 to n-1 do
			if not (List.mem k !antTraj) then begin 
				voisins := k::!voisins;
				probas := probasMat.(u).(k)::!probas; end
			done;
		probas := normalise !probas (somme !probas);
		let probaCumul = Array.make (List.length !probas) 0. in
		
		
		let probaTab = Array.of_list (!probas) in
		probaCumul.(0) <- probaTab.(0);
		
		for i = 1 to (Array.length probaCumul) -1 do
			probaCumul.(i) <- probaCumul.(i-1) +. probaTab.(i);
			done;
			
		let p = Random.float 1.0 in
		let rec recherche i =
			if i = Array.length probaCumul -1 then i
			else if probaCumul.(i+1) >= p then i+1
			else recherche (i+1) in
		
		List.nth !voisins (recherche 0)
		in
		
	let rec updatePheromones (antTraj, antCout) = match antTraj with
		[] -> ()
		|a::[] -> ()
		|a::b::q -> begin let c = pheromones.(a).(b) in pheromones.(a).(b) <- c +. (1./.antCout); updatePheromones (q,antCout) end
		in
		
	let pheromonesDissipation () = 
		for i = 0 to n-1 do
			for j = 0 to n-1 do
				pheromones.(i).(j) <- (1. -. rho) *. pheromones.(i).(j);
			done;
		done;
		in
		
	let executeFourmi ant =
		let antTraj,antCout = ant in
		let k = ref 1 in
		let depart = Random.int n in
		antTraj := [depart];
		while !k < n do
			antTraj := transition (List.hd !antTraj) ant ::!antTraj;
			k:= !k+1
			done;
		antCout := longueur graphe !antTraj;
		() in
		
	for k = 0 to duree do
		Array.iter (fun (a,b) -> executeFourmi (a,b); updatePheromones (!a,!b)) ants;
		pheromonesDissipation ();
		done;
	executeFourmi ants.(0);
	let traj,cout = ants.(0) in
	!traj;;


let genApprox (n,graphe) =
	let ecartMin = 1. in
	let taillePop = 100 in
	let genMax = 200 in
	
	
	let crossover t1 t2 =
		let k = int_of_float(0.3*.float_of_int n) in
		let rec divise l c = match l with
			[] -> [],[]
			|a::p -> if c = k then [a],p else begin let l1,l2 = divise p (c + 1) in a::l1,l2 end
			in
		let rec fusion l lbis = match l,lbis with
			[],_ -> lbis
			|_,[] -> l
			|a::p,_ -> a::(fusion p lbis)
		in
		let l1 = fst (divise t1 1) in
		let notInListe a = not (List.mem a l1) in
		let l2 = List.filter notInListe t2 in
		fusion l1 l2
		in
	
	let rec optLocale l = match l with
		a::b::c::d::p -> begin 
										let d0 = distance graphe a b +. distance graphe c d in
										let d1 = distance graphe c b +. distance graphe a d in
										let d2 = distance graphe a c +. distance graphe b d in
										if d1 < d0 || d2 < d0 then begin
											if d1 < d2 then c::b::a::d::optLocale p
											else a::c::b::d::optLocale p end
											else a::b::c::d::optLocale p
								end
		|_ -> l
		in
	
	let optReverse l = 
		let m1 = Random.int n in
		let i = ref (Random.int n) in
		while m1 = (!i) do
			i := Random.int n;
		done;
		let m2 = !i in
		let n1, n2 = if m1 < m2 then m1, m2 else m2, m1 in
		let t = Array.of_list l in
		
		let l1 = Array.to_list (Array.init n1 (fun j -> t.(j)) ) in
		let l2 = Array.to_list (Array.init (n-n2-1) (fun j -> t.(n2 + j +1))  ) in
		let rev = ref [] in
		for j = n1 to n2 do
			rev := t.(j)::(!rev);
		done;
		let lRev = (l1@(!rev))@l2 in
		
		if longueur graphe lRev < longueur graphe l then lRev  else l
		in
	
	let nearest k visite = 
			let m = ref infinity in
			let pos = ref 0 in
			let enVisite = ref true in
			let j = ref 0 in
			while !j < n && !enVisite do
				let i = !j in
				j := i +1;
				let d = distance graphe k i in
				if visite.(i) = 0 && d < !m then
					begin visite.(i) <- 1; enVisite := false; pos := i; m := d; end
				
			done;
			!pos
			in
			
	
	let swap path i j =
		if i = j then path
		else
			begin
			let n1, n2 = if i < j then i, j else j,i in
			let t = Array.of_list path in
			let l1 = if n1 > 0 then Array.to_list (Array.init n1 (fun k -> t.(k)) ) else [] in
			let l2 = if n2 < n-1 then Array.to_list (Array.init (n - n2) (fun k -> t.(n2 + k )) ) else [] in
			let rev = ref [] in
			for k = n1 to n2 do
				rev := t.(k)::(!rev);
			done;
			l1@(!rev)@l2
			end
		in
	
	let twoOpt path =
		let length = longueur graphe in
		let d = ref (length path) in
		let optPath = ref path in
		(*for i = 0 to n-2 do
			for j = i+1 to n-1 do
				let l = swap path i j in
				let len = length l in
				if len < (!d) then begin d := len; optPath := l; end
			done;
		done;*)
		
		let i = ref 0 in
		let loop = ref true in
		while (!i) < n-2 && (!loop) do
			let j = ref (!i + 1) in
			while !j < n && !loop do
				let l = swap path (!i) (!j) in
				let len = length l in
				j := !j + 1;
				if len < !d then begin loop := false; optPath := l; end
				
			done;
			i := !i +1;
		done;
		
		!optPath
		in
	
	
	let rec twoOptRec path =
		let eps = 0.99 in
		let length = longueur graphe in
		let d = ref (length path) in
		let optPath = ref path in
		(*for i = 0 to n-2 do
			for j = i+1 to n-1 do
				let l = swap path i j in
				let len = length l in
				if len < (!d) then begin d := len; optPath := l; end
			done;
		done;*)
		
		let i = ref 0 in
		let loop = ref true in
		while (!i) < n-2 && (!loop) do
			let j = ref (!i + 1) in
			while !j < n && !loop do
				let l = swap path (!i) (!j) in
				let len = length l in
				j := !j + 1;
				if len < eps *. !d then begin loop := false; optPath := twoOptRec l; end
				
			done;
			i := !i +1;
		done;
		
		!optPath
		in
	
	let greedy () =
		let aVisiter = Array.make n 0 in
		let k = Random.int n in
		aVisiter.(k) <- 1;
		let l = ref [k] in
		
		for i = 1 to n-1 do
			l := (nearest (List.hd !l) aVisiter)::(!l);
		done;
		!l
		in
		
	let pop = Array.init taillePop (fun i -> greedy ()) in
	
	let cond1 l = (*renvoie true iff for all i, |longueur i - longuer| > a*)
		let d = longueur graphe l in
		let i = ref 0 in
		let cond = ref true in
		while (!i < taillePop) && (!cond) do
			cond := Float.abs (d -. longueur graphe pop.(!i)) > ecartMin;
			i := !i +1;
		done;
		!cond
		in
	
	let cond2 l = (*renvoie true iff il existe i tq longueur < longueur i*)
		let d = longueur graphe l in
		let i = ref 0 in
		let cond = ref false in
		while !i < taillePop && not (!cond) do
			cond := d < longueur graphe pop.(!i);
			i := !i +1;
		done;
		!cond
		in 
	
	let comp l1 l2 =
		let d1, d2 = longueur graphe l1, longueur graphe l2 in
		if d1=d2 then 0
		else if d1 > d2 then 1
		else -1
		in
		
		
	
	Array.fast_sort comp pop;
	
	let selectionParents () = (*$ fois plus de chance de choisir un chemin court, p = 4/5 = 0.8*)
		let m = taillePop / 2 in
		let i = Random.int m + if Random.float 1. < 0.8 then 0 else m in
		let r = if Random.float 1. < 0.8 then 0 else m in
		let j = ref (Random.int m + r) in
		while i = !j do
			j := Random.int m + r;
		done;
		pop.(i),pop.(!j)
		in
	
	for i = 1 to genMax do
		let l1,l2 = pop.(0), pop.(1) in
		(*let traj = ref (optLocale (crossover l1 l2)) in*)
		let path = twoOptRec (crossover l1 l2) in
		let l = ref path in
		(*for k = 0 to (n/5) do
			l := twoOpt (!l);
		done;*)
		
		if cond1 !l && cond2 !l then
			begin
			(*print_string "ok";
			print_newline ();*)
			pop.(taillePop - 1) <- !l;
			Array.fast_sort comp pop;
			end
	done;
	
	pop.(0)
;;

let dynApprox () =
	let eps = 2. in
	let largeur = ceil (float_of_int (8*n) /. eps) in
	let lInt = int_of_float largeur in
	let grille = Array.make_matrix (lInt + 1) (lInt + 1) 0 in
	let grillePoints = Array.make_matrix (lInt + 1) (lInt + 1) [] in
	for k = 0 to n-1 do
		let (x,y),l = graphe.(k) in
		grille.(int_of_float (Float.round x)).(int_of_float (Float.round y)) <- 1;
		grillePoints.(int_of_float (Float.round x)).(int_of_float (Float.round y)) <- (x,y)::grillePoints.(int_of_float (Float.round x)).(int_of_float (Float.round y));
	done;
	
	let rec pow l k =
		if k >= 2*l then [k]
		else k::(pow l (2*k))
	in
	
	let powListe = pow lInt 1 in
	powListe
	;;

let rec convertiTraj l graphe = match l with
	[] -> []
	|a::p -> let (x,y),t = graphe.(a) in (x,y)::convertiTraj p graphe;;

let timeIt f g = 
	let time = Sys.time() in
	let traj = f g in
	traj,Sys.time() -. time;;

let writeArray t fichier =
	let n= Array.length t in
	for k = 0 to n-1 do
		Printf.fprintf fichier "%f \n" t.(k) ;
	done;
	close_out fichier;;

let compileData m =
	
	let trajetsPrim = Array.make m 0. in
	let dureePrim = Array.make m 0. in
	
	let trajetsAnts = Array.make m 0. in
	let dureeAnts = Array.make m 0. in
	
	let trajetsGen = Array.make m 0. in
	let dureeGen = Array.make m 0. in
	
	for n = 2 to m+1 do
		let moyPrim = ref 0. in
		let tempsPrim = ref 0. in
		
		let moyAnts = ref 0. in
		let tempsAnts = ref 0. in
		
		let moyGen = ref 0. in
		let tempsGen= ref 0. in
		
		for k = 0 to 9 do
			let graphe = nouveauGraphe n in
			let trajPrim, tPrim = timeIt primApprox (n,graphe) in
			let trajAnts, tAnts = timeIt primApprox (n,graphe) in
			let trajGen, tGen = timeIt genApprox (n,graphe) in
			
			moyPrim := !moyPrim +. longueur graphe trajPrim;
			tempsPrim := !tempsPrim +. tPrim;
			
			moyAnts:= !moyAnts +. 1. +. longueur graphe trajAnts;
			tempsAnts := !tempsAnts +. tAnts;
			
			moyGen := !moyGen +. longueur graphe trajGen;
			tempsGen := !tempsGen +. tGen;
		done;
		
		trajetsPrim.(n-2) <- !moyPrim /. 10. ;
		dureePrim.(n-2) <- !tempsPrim /. 10. ;
		
		trajetsAnts.(n-2) <- !moyAnts /. 10. ;
		dureeAnts.(n-2) <- !tempsAnts /. 10. ;
		
		trajetsGen.(n-2) <- !moyGen /. 10. ;
		dureeGen.(n-2) <- !tempsGen /. 10. ;
		
	done;
	
	let fTrajPrim = open_out "C:\\Users\\adam0\\Desktop\\TIPE 2 le retour\\DisPrim2.txt"in
	writeArray trajetsPrim fTrajPrim;
	let fDureePrim = open_out "C:\\Users\\adam0\\Desktop\\TIPE 2 le retour\\TempsPrim2.txt" in
	writeArray dureePrim fDureePrim;
	
	let fTrajAnts = open_out "C:\\Users\\adam0\\Desktop\\TIPE 2 le retour\\DisAnts2.txt" in
	writeArray trajetsAnts fTrajAnts;
	let fDureeAnts = open_out "C:\\Users\\adam0\\Desktop\\TIPE 2 le retour\\TempsAnts2.txt" in
	writeArray dureeAnts fDureeAnts;
	
	let fTrajGen = open_out "C:\\Users\\adam0\\Desktop\\TIPE 2 le retour\\DisGen.txt" in
	writeArray trajetsGen fTrajGen;
	let fDureeGen = open_out "C:\\Users\\adam0\\Desktop\\TIPE 2 le retour\\TempsGen.txt" in
	writeArray dureeGen fDureeGen;
 ();;

let compileDataBis m =
	
	let trajetsPrim = Array.make m 0. in
	let dureePrim = Array.make m 0. in
	
	let trajetsAnts = Array.make m 0. in
	let dureeAnts = Array.make m 0. in
	
	
	for n = 2 to m+1 do
		print_int n;
		print_newline ();
		let moyPrim = ref 0. in
		let tempsPrim = ref 0. in
		
		let moyAnts = ref 0. in
		let tempsAnts = ref 0. in
		
		
		for k = 0 to 9 do
			let graphe = nouveauGraphe n in
			let trajPrim, tPrim = timeIt primApprox (n,graphe) in
			let trajAnts, tAnts = timeIt primApprox (n,graphe) in
			
			moyPrim := !moyPrim +. longueur graphe trajPrim;
			tempsPrim := !tempsPrim +. tPrim;
			
			moyAnts:= !moyAnts +. 1. +. longueur graphe trajAnts;
			tempsAnts := !tempsAnts +. tAnts;
			
		done;
		
		trajetsPrim.(n-2) <- !moyPrim /. 10. ;
		dureePrim.(n-2) <- !tempsPrim /. 10. ;
		
		trajetsAnts.(n-2) <- !moyAnts /. 10. ;
		dureeAnts.(n-2) <- !tempsAnts /. 10. ;
		
		
	done;
	
	let fTrajPrim = open_out "C:\\Users\\adam0\\Desktop\\TIPE 2 le retour\\DisPrim2.txt"in
	writeArray trajetsPrim fTrajPrim;
	let fDureePrim = open_out "C:\\Users\\adam0\\Desktop\\TIPE 2 le retour\\TempsPrim2.txt" in
	writeArray dureePrim fDureePrim;
	
	let fTrajAnts = open_out "C:\\Users\\adam0\\Desktop\\TIPE 2 le retour\\DisAnts2.txt" in
	writeArray trajetsAnts fTrajAnts;
	let fDureeAnts = open_out "C:\\Users\\adam0\\Desktop\\TIPE 2 le retour\\TempsAnts2.txt" in
	writeArray dureeAnts fDureeAnts;
	
 ();;




open_graph(" " ^ string_of_int t ^"x" ^ string_of_int t);;

(*let pred = primApproxTree (n,graphe) in
drawTree pred;;*)

drawTrajets graphe ([antApprox (n,graphe)]);;


drawTrajets graphe ( [bruteForce graphe]);;

(*let fichier = open_out "C:\\Users\\adam0\\Desktop\\TIPE 2 le retour\\test.txt";;
fichier;;
Printf.fprintf fichier "%d %d\n" 1 2;;
close_out fichier;;*)
(*exit 0;;*)



(*
let time = ref 0. in
for k = 0 to 10 do
	time := !time +. timeIt main graphe;
	done;
print_float !time;;*)