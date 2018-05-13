/*

Nombre: md.mc.ml.mod
Autor: F. Javier Perez (https://gist.github.com/ImJaviPerez/)
Fecha: 11-04-2018
version: 1.0

https://gist.github.com/ImJaviPerez/

Descripcion:
Este programa esta basado en un articulo de 
Alinaghian, Mahdi & Shokouhi, Nadia, 2018. 
"Multi-depot multi-compartment vehicle routing problem, solved by a hybrid adaptive large neighborhood search,"
Omega, Elsevier, vol. 76(C), pages 85-99. 
https://www.sciencedirect.com/science/article/pii/S0305048316303553
https://ideas.repec.org/a/eee/jomega/v76y2018icp85-99.html


Este programa fuciona con un fichero externo de datos.
- Debe tener el mismo nombre que este programa con la extension ".dat"
- En Gusek se debe habilitar la opcion: "Tools > Enable use of external data files"

TO-DO:
Esta sin acabar:
- No se usan los dos depositos si ponemos 1 solo vehiculo en el deposito 1 y 
3 en el segundo deposito el programa no encuentra solucion.
¿Ver la restriccion 10?

- Hay que asignar cada vehiculo a un deposito usando el parametro DQ[r in ND, k in K].
(no la variable u[k])
# Quizas una mejor forma de definirlo seria:
# param DQ{i in ND, k in K}, binary; 
# Vale 1 si el k-esimo vehiculo esta en ese deposito y 0 en caso contrario
# Ejemplo:
#     Supongamos que tenemos 2 depositos y 5 vehiculos en total:
# param : ND_x_K : DQ :=
#        1  1   1    # Indica que en el deposito 1, el vehiculos 1; SI esta disponible.
#        1  2   1    # Indica que en el deposito 1, el vehiculos 2; SI esta disponible.
#        1  3   0    # Indica que en el deposito 1, el vehiculos 3; NO esta disponible.
#        1  4   0    # Indica que en el deposito 1, el vehiculos 4; NO esta disponible.
#        1  5   0    # Indica que en el deposito 1, el vehiculos 5 NO esta disponible.
#        2  1   0    # Indica que en el deposito 2, el vehiculos 1; NO esta disponible.
#        2  2   0    # Indica que en el deposito 2, el vehiculos 2; NO esta disponible.
#        2  3   1    # Indica que en el deposito 2 el vehiculos 3 SI esta disponible.
#        2  4   1    # Indica que en el deposito 2, el vehiculos 4; SI esta disponible.
#        2  5   1    # Indica que en el deposito 2, el vehiculos 5; SI esta disponible.
O sea que en el deposito 1 tendriamos 2 vehiculos y en el deposito 3 tendriamos 3 vehiculos.
y crear una restriccion del estilo:
s.t. restriccion_10_u{r in ND}: sum{k in K} u[k] <= sum{k in K} DQ[r,k];

- Esto anterior implica que hay que limitar u[k] con DQ[i,k] en todas las restricciones.
- No es necesario modificar el parametro fk (gasto fijo por vehiculo) ni la variable u[k].

- Eso implica una nueva restriccion que relacione el vehiculo u[k] con x[i,j,k] y con la 
distancia c[i,j] (para i in ND). O sea, cuando el vehiculo sale de su deposito, 
la distancia inicial se mide desde ese deposito.
*/

# DECLARACION DE VARIABLES ---------------
# numero de nodos
## param num_nodos, integer, >= 2;
param num_depositos, integer, >= 1;
param num_clientes, integer, >= 1;
param num_productos, integer, >= 1; 
param num_vehiculos, integer, >= 1;


# CONJUNTOS basicos ----------------------
# ND el conjunto de depositos
set ND := 1..num_depositos; ####(num_clientes+1)..num_nodos;
# Nv el conjunto de clientes
# Set ND := 1..1
set Nv := (num_depositos+1)..(num_depositos+num_clientes); ####num_clientes;
#### set Nv := 2..4;

# Ntot el conjunto de todos los nodos ###; denotado por los indices i y j
# O sea ND y Nv son subconjuntos disjuntos de Ntot
set Ntot := ND union Nv;
# set Ntot := 1..num_nodos;





# G el conjunto de productos; denotado por el indice g
set G := 1..num_productos;

# K el conjunto de vehiculos; denotado por el indice k
set K := 1..num_vehiculos;

# CONJUNTOS compuestos y PARAMETROS ----------------------
# d_ig demanda del nodo i para el producto g
#### param d{i in Ntot, g in G};
param d{i in Nv, g in G};

# Ntot_x_Ntot = conjunto todos los arcos entre nodos
# c[i,j] = distancia del nodo i al j 
param c{i in Ntot, j in Ntot};

# Q_g la capacidad del compartimento del vehiculo dedicado al producto g
## K_x_G = conjunto vehiculos por producto
# #### ¿SOLO DEPENDE DEL PRODUCTO?¿NO DEPENDE DEL VEHICULO?
############### g o (k, g) ????????????????????????????????
param Q{g in G};

## # DQ_i el numero maximo de vehiculos que salen del deposito i
## param DQ{i in ND};
# DQ_ik la lista de vehiculos k que salen del deposito i
param DQ{i in ND, k in K}, binary; 
# Quizas una mejor forma de definirlo seria:
# param DQ{i in ND, k in K}, binary; 
# Vale 1 si el k-esimo vehiculo esta en ese deposito y 0 en caso contrario
# Ejemplo:
#     Supongamos que tenemos 2 depositos y 5 posibles vehiculos por deposito:
# param : ND_x_K : DQ :=
#        1  1   1    # Indica que en el deposito 1, el vehiculos 1; SI esta disponible.
#        1  2   0    # Indica que en el deposito 1, el vehiculos 2; NO esta disponible.
#        1  3   1    # Indica que en el deposito 1, el vehiculos 3; SI esta disponible.
#        1  4   0    # Indica que en el deposito 1, el vehiculos 4; NO esta disponible.
#        1  5   0    # Indica que en el deposito 1, el vehiculos 5 NO esta disponible.
#        2  1   1    # Indica que en el deposito 2, el vehiculos 1; SI esta disponible.
#        2  2   1    # Indica que en el deposito 2, el vehiculos 2; SI esta disponible.
#        2  3   1    # Indica que en el deposito 2 el vehiculos 3 SI esta disponible.
#        2  4   1    # Indica que en el deposito 2, el vehiculos 4; SI esta disponible.
#        2  5   0    # Indica que en el deposito 2, el vehiculos 5; NO esta disponible.


# MC la distancia maxima, que cada vehiculo se permite viajar
# param MC{k in K};
param MC, integer, >= 1;

# fk el costo fijo de usar el vehiculo k
param fk{k in K}, >= 0;

# M un numero muy grande
param M, integer, >= 1;



# VARIABLES DE DECISION
# x_ijk equivalen a 1 si la ruta entre los nodos i y j es recorrida por el vehiculo k, y es cero; en caso contrario
# Segun la restriccion 14, x_ijk es binaria
# var x{i in Ntot, j in Ntot, k in K}, binary;
# var x{i in ND, j in Nv, k in K}, binary;
var x{i in Ntot, j in Ntot, k in K}, binary;

# y_igk igual a 1 si la demanda del nodo i para el producto g es entregada por el vehiculo k;es cero, de lo contrario
# Segun la restriccion 14, y_igk es binaria
##### var y{i in Ntot, g in G, k in K}, binary;
var y{i in Nv, g in G, k in K}, binary;

# u_k igual a 1 si el vehiculo k es usado, 0 en caso contario
var u{k in K}, binary;

# ST_ik se usa para la eliminacion de sub-tours
# ############### ¿ES ENTERO???????????????????????
var ST{i in Ntot, k in K}, integer;


########## EN LAS RESTRICCIONES 
######### ¿NO HAY QUE PONER UNA RESTRICCION DEL TIPO 
######### "i != j" PARA EVITAR QUE SE VAYA DE UN NODO AL MISMO NODO????????????

# FUNCION OBJETIVO Y RESTRICCIONES ---------------
# Eq. (1 ) is the objective function, which includes two sections,
# the first section is related to minimizing the total traveled distance,
# and the second section is related to the fixed cost for using
# the vehicles.
# La funcion objetivo minimiza el costo (longitud) del camino recorrido
minimize zObjetivo_1: sum{i in Ntot, j in Ntot, k in K: i!= j} c[i,j] * x[i,j,k] + sum{k in K} fk[k] * u[k];


# Restriccion 2:
# Constraint ( 2 ) indicates that in case each vehicle
# is used, then it should start its tour from a depot. This constraint
# also indicates that each vehicle can ultimately leave the depot only
# once.
## s.t. restriccion_2{k in K} : sum{i in ND, j in Nv} x[i,j,k] <= u[k];
s.t. restriccion_2{k in K} : sum{i in ND, j in Nv} x[i,j,k] * DQ[i,k]<= u[k];

# Restriccion 3:
# Constraint ( 3 ) states that each customer’s demand for a given
# product must be delivered by a single vehicle. Constraints
s.t. restriccion_3{i in Nv, g in G}: sum{k in K} y[i,g,k] = 1;

# Restriccion 4:
# Constraints ( 4 ) and ( 5 ) state that the demand of customer i for products g can be fulfilled
# by vehicle k only when this vehicle visits customer i .
s.t. restriccion_4{i in Nv, k in K}: sum{g in G} y[i,g,k] <= (M * sum{j in Ntot: i!= j} x[j,i,k]);

# Restriccion 5:
s.t. restriccion_5{k in K, i in Nv}: sum{j in Ntot: i!= j} x[j,i,k] <=  sum{g in G} y[i,g,k];

# Restriccion 6:
# Constraint ( 6 ) ensures that each vehicle visits any given customer at
# most once.
s.t. restriccion_6{j in Nv, k in K}: sum{i in Ntot: i!= j} x[i,j,k] <= 1;

# Restriccion 7:
# Constraint ( 7 ) states that any vehicle that enters a node
# should also depart from that node.
s.t. restriccion_7{j in Ntot, k in K}: sum{i in Ntot: i!= j} x[i,j,k] = sum{i in Ntot: i!= j} x[j,i,k];

# Restriccion 8:
# Constraint ( 8 ) limits the capacity
# of vehicles
s.t. restriccion_8{g in G, k in K}: sum{i in Nv} y[i,g,k] * d[i,g] <= Q[g];

# Restriccion 9:
# constraint ( 9 ) limits the maximum distance.
s.t. restriccion_9{k in K}: sum{i in Ntot, j in Ntot: i!= j} c[i,j] * x[i,j,k] <= MC;

# Restriccion 10:
# Constraint ( 10 ) is related to the capacity of depots.
## ORIGINAL s.t. restriccion_10{i in ND}: sum{k in K, j in Nv} x[i,j,k] <= DQ[i];
#s.t. restriccion_10{i in ND}: sum{k in K, j in Nv} x[i,j,k] <= sum{k in K} DQ[i,k];
### s.t. restriccion_10_x{i in ND, j in Nv}: sum{k in K} x[i,j,k] <= DQ[i];
s.t. restriccion_10_u{i in ND}: sum{k in K} u[k] * DQ[i,k] <= sum{k in K} DQ[i,k];

# Restriccion 11:
# Constraints ( 11 )
# and ( 12 ) are used for elimination of sub-tours.
s.t. restriccion_11: sum{i in ND, k in K} ST[i,k] = 0;

# Restriccion 12:
s.t. restriccion_12{i in Ntot, j in Nv, k in K}: ST[i,k] + 1 <= ST[j,k] + M * (1 - x[i,j,k]);

# Restriccion 14:
# And constraints ( 13 ) and ( 14 ) define the domains of decision variables.
s.t. restriccion_13{i in Ntot,k in K}: ST[i,k] >= 0;


######################################
######################################

# Restriccion para vehiculos: Se deben usar los vehiculos indicados por x[i,j.k]
### s.t. restriccion_vehiculos{k in K, i in Ntot, j in Ntot: i!= j}: u[k] >= x[i,j,k];
s.t. restriccion_vehiculos{v in Nv, g in G, k in K}: u[k] >= y[v,g,k];

#Restriccion para obligar a que si un vehiculo sale de un deposito, entonces x[i,j,k] debe ser 1
### s.t. restriccion_Depot2 : sum{i in ND, j in Nv, k in K} x[i,j,k] >= sum{k in K} u[k];
## s.t. restriccion_Depot2 {k in K} : sum{i in ND, j in Nv} x[i,j,k] >= u[k];

s.t. restriccion_Depot2 {k in K} : sum{i in ND, j in Nv} x[i,j,k] * DQ[i,k] >= u[k];

# s.t. restriccion_5bis{k in K, i in Nv, g in G}: sum{j in Ntot: i!= j} x[j,i,k] >= y[i,g,k];

######################################
######################################



# RESOLUCION 
solve;

# MOSTRAR DATOS E INFO ---------------

/*
printf ("\n\n--------------------------------------------------");
printf ("\n------ -COMPROBACIÓN DE DATOS ----------------------");
printf("\nNodos.Ntot\n");
printf{i in Ntot} "  %3d", i;

printf("\nDepositos.ND\n");
printf{i in ND} "  %3d", i;

printf("\nClientes.Nv\n");
printf{i in Nv} "  %3d", i;

printf("\nProductos.G\n");
printf{g in G} "  %3d", g;

printf("\nVehiculos.K\n");
printf{k in K} "  %3d", k;

printf("\n\nNod.Orig.I   Nod.Dest.J   Distan.C\n");
printf{i in Ntot, j in Ntot} "  %3d        %3d       %6d\n", i, j, c[i,j];

printf("\nNod.I  num.Product  Demanda.produc.d_ig\n");
printf{i in Nv, g in G} "  %3d    %3d           %6d\n", i, g, d[i,g];

printf("\nCompartiment.Produc.g.Q_g\n");
printf{g in G} "  %3d     %6d\n", g, Q[g];

## printf("\nNodo.D   Max.num.vehic.del.deposito.DQ_i\n");
## printf{i in ND} "  %3d                %6d\n", i, DQ[i];

printf("\nNodo.D  Vehic.K  Vehic.En.Deposito.DQ_ik\n");
printf{i in ND, k in K} "  %3d      %3d       %6d\n", i, k, DQ[i,k];

printf("\nNum.vehic.k   Coste.fijo.vehic.fk\n");
printf{k in K} "  %3d              %6d\n", k, fk[k];

printf("\n  k    Vehic.usado.u_k\n");
printf{k in K} "%3d     %6d\n", k, u[k];

printf("\n\Nodo.i   Vehic.k      SubTour.ST_ik\n");
printf{i in Ntot, k in K} " %3d      %3d       %6d\n", i, k, ST[i,k];

printf ("\n-------------- FIN COMPROBACION ------------------");
printf ("\n--------------------------------------------------");
*/

printf ("\n\n--------------------------------------------------");
printf ("\n--------------------------------------------------");
printf "\n\nEl camino optimo recorre una distancia = %d",   sum{i in Ntot, j in Ntot, k in K: i!=j} c[i,j] * x[i,j,k];
printf "\n\nLa distancia maxima recorrida por un vehiculo es = %d", MC;

printf("\n\nEl recorrido de cada vehiculo es:\n Num.Vehíc.K  Distan.C\n");
# printf{k in K:  u[k] == 1} "  %3d    \t   %6d\n", k, sum{i in Ntot, j in Ntot : i!=j} (c[i,j] * x[i,j,k]);
printf{k in K} "  %3d    \t   %6d\n", k, sum{i in Ntot, j in Ntot : i!=j} (c[i,j] * x[i,j,k]);

printf("\n\nEl recorrido de nodo a nodo es:\n  Nd.Orig.I  Nd.Dest.J  Num.Vehíc.K  Distan.C\n");
printf{k in K, i in Ntot, j in Ntot :  x[i,j,k] == 1} "  %3d    \t %3d  \t %3d \t  %6d\n", i, j, k, c[i,j];

printf ("\n--------------------------------------------------");
printf "\n\nEl recorrido optimo tiene un coste fijo %d",   sum{k in K} fk[k] * u[k];

printf("\n\nVehíc.K  Coste.fijo.fk = \n");
printf{k in K : u[k] == 1} "  %3d  \t  %6d\n", k, fk[k];

/*
printf ("\n--------------------------------------------------");
# printf("\n\nVehíc.K  Nd.Orig.I Nd.Dest.J  Produc.G   Cantida.D\n");
# printf{k in K, i in Ntot, j in Ntot, v in Nv, g in G : x[i,j,k] == 1 && i!=j && u[k] == 1} "  %3d \t %3d    \t %3d   \t %3d   \t %6d\n", k, i, j, g, d[j,g];
printf("\n\nNd.I \t Nd.V \t Vehic.K \t x_ijk \t u_k \t y_igk\n");
printf{i in Ntot, v in Nv, k in K, g in G : i!=v} "  %3d \t %3d \t %3d \t %3d \t %3d \t %3d\n", i, v, k, x[i,v,k], u[k], y[v,g,k];
*/


/*
printf ("\n--------------------------------------------------");
printf("\n\nSub-tours:\nVehíc.K  Nd.Orig.I  ST_ik  \n");
printf{k in K, i in Ntot} "  %3d \t %3d \t %6d\n", k, i, ST[i,k];
*/

/*
printf ("\n--------------------------------------------------");
printf("\n\nNd.Dest.V \t Prod.G \t Vehíc.K \t u_k \t Y_igk \n");
printf{v in Nv, g in G, k in K } "  %3d \t %3d \t %3d \t %3d \t %3d\n", v, g, k, u[k], y[v,g,k];
*/
printf ("\n--------------------------------------------------");
printf("\n\nNd.Orig.I \t Nd.Dest.J \t Vehíc.K \t u_k \t X_ijk \n");
printf{k in K , i in Ntot, j in Ntot: i != j && x[i,j,k] == 1} "  %3d \t %3d \t %3d \t %3d \t %3d\n", i, j, k, u[k], x[i,j,k];


printf ("\n--------------------------------------------------");
printf("\n\nNum salidas de un deposito:");
printf("\nNum.Depos.D \t Num.Salidas. \t Salidas.Max.DQ\n");
printf{i in ND} "  %3d \t %6d \t %6d\n", i, sum{k in K, j in Nv} x[i,j,k], sum{k in K} DQ[i,k];


/*
printf("\n\nEl recorrido de nodo a nodo es:\nVehic.K   Nd.Orig.I  Nd.Dest.J   X.ijk  \n");
printf{k in K, i in Ntot, j in Ntot} "  %3d \t %3d \t %3d \t %3d\n", k, i, j, x[i,j,k];
*/


# DATOS USADOS EN ESTE PROBLEMA ---------------
set Ntot_x_Ntot, within Ntot cross Ntot;
set Nv_x_G within Nv cross G;
set ND_x_K within ND cross K;
# Los datos se encuentran en el fichero .dat
# data;


end;
