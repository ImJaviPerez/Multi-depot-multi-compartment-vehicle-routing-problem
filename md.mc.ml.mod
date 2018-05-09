/*

Nombre: md.mc.ml.mod
Autor: F. Javier Perez
Fecha: 11-04-2018
version: 1.0

Descripcion:
Este programa fuciona con un fichero externo de datos.
- Debe tener el mismo nombre que este programa con la extension ".dat"
- En Gusek se debe habilitar la opcion: "Tools > Enable use of external data files"

TO-DO:

*/

# DECLARACION DE VARIABLES ---------------
# numero de nodos
param num_nodos, integer, >= 2;
param num_depositos, integer, >= 1;
param num_clientes, integer, >= 1;
param num_productos, integer, >= 1;
param num_vehiculos, integer, >= 1;




# CONJUNTOS basicos ----------------------
# Ntot el conjunto de todos los nodos ###; denotado por los indices i y j
set Ntot := 1..num_nodos;

# ND el conjunto de depositos
set ND := 1..num_depositos;

# Nv el conjunto de clientes
set Nv := 1..num_clientes;

# G el conjunto de productos; denotado por el indice g
set G := 1..num_productos;

# K el conjunto de vehiculos; denotado por el indice k
set K := 1..num_vehiculos;

# CONJUNTOS compuestos y PARAMETROS ----------------------
# d_ig demanda del nodo i para el producto g
param d{i in Ntot, g in G};

# Ntot_x_Ntot = conjunto todos los arcos entre nodos
# c[i,j] = distancia del nodo i al j 
param c{i in Ntot, j in Ntot};

# Q_g la capacidad del compartimento del vehiculo dedicado al producto g
## K_x_G = conjunto vehiculos por producto
# #### �SOLO DEPENDE DEL PRODUCTO?�NO DEPENDE DEL VEHICULO?
############### g o (k, g) ????????????????????????????????
param Q{g in G};

# DQ_i el numero maximo de vehiculos que salen del deposito i
param DQ{i in ND};

# MC la distancia maxima, que cada vehiculo se permite viajar
# param MC{k in K};
param MC :=  1000;

# fk el costo fijo de usar el vehiculo k
param fk{k in K};


# M un numero muy grande
param M :=  1e10; #infinity



# VARIABLES DE DECISION
# x_ijk equivalen a 1 si la ruta entre los nodos i y j es recorrida por el vehiculo k, y es cero; en caso contrario
# Segun la restriccion 14, x_ijk es binaria
# var x{i in Ntot, j in Ntot, k in K}, binary;
var x{i in ND, j in Nv, k in K}, binary;

# y_igk igual a 1 si la demanda del nodo i para el producto g es entregada por el vehiculo k;es cero, de lo contrario
# Segun la restriccion 14, y_igk es binaria
var y{i in Ntot, g in Ntot, k in K}, binary;

# u_k igual a 1 si el vehiculo k es usado, 0 en caso contario
var u{k in K}, binary;

# ST ik variable used for elimination of sub-tours
# ############### �ES ENTERO???????????????????????
var ST{i in Ntot, k in K}, integer;


########## EN LAS RESTRICCIONES 
######### �NO HAY QUE PONER UNA RESTRICCION DEL TIPO 
######### "i != j" PARA EVITAR QUE SE VAYA DE UN NODO AL MISMO NODO????????????

# FUNCION OBJETIVO Y RESTRICCIONES ---------------
# La funcion objetivo minimiza el costo (longitud) del camino recorrido
minimize zObjetivo_1: sum{i in Ntot, j in Ntot, k in K} c[i,j] * x[i,j,k] + sum{k in K} fk[k] * u[k];

# Restriccion 2:
s.t. restriccion_2{k in K} : sum{i in ND, j in Nv} x[i,j,k] <= u[k];

# Restriccion 3:
s.t. restriccion_3{i in Nv, g in G}: sum{k in K} y[i,g,k] = 1;

# Restriccion 4:
s.t. restriccion_4{i in Nv, k in K}: sum{g in G} y[i,g,k] <= M;
### SIM EMBARGO LA RESTRICCION 4 PARACE SER 2 RESTRICCIONES A LA VEZ
# ????????????????????????????????????????????????????????

# Restriccion 5:
### SE HA CAMBIADO EL ORDEN DE LOS INDICES x_ijk <--> x_jik
s.t. restriccion_5{k in K, i in Nv}: sum{j in Ntot} x[j,i,k] <=  sum{g in G} y[i,g,k];
# ????????????????????????????????????????????????????????

# Restriccion 6:
s.t. restriccion_6{j in Nv, k in K}: sum{i in Ntot} x[j,i,k] <= 1;

# Restriccion 7:
s.t. restriccion_7{j in Ntot, k in K}: sum{i in Ntot} x[i,j,k] = sum{i in Ntot} x[j,i,k];

# Restriccion 8:
s.t. restriccion_8{g in G, k in K}: sum{i in Nv} y[i,g,k] * d[i,g] <= Q[g];

# Restriccion 9:
s.t. restriccion_9{k in K}: sum{i in Ntot, j in Nv} c[i,j] * x[i,j,k] <= MC;

# Restriccion 10:
s.t. restriccion_10{i in ND}: sum{k in K, j in Nv} x[i,j,k] <= DQ[i];

# Restriccion 11:
s.t. restriccion_11: sum{i in ND, k in K} ST[i,k] = 0;

# Restriccion 12:
s.t. restriccion_12{i in Ntot, j in Nv, k in K}: ST[i,k] + 1 <= ST[j,k] + M * (1 - x[i,j,k]);

# Restriccion 13:
s.t. restriccion_13{i in Ntot,k in K}: ST[i,k] >= 0;



# RESOLUCION 
solve;

# MOSTRAR DATOS E INFO ---------------
printf("Nodo Origen   Nodo destino   Veh�culo   Distancia   Conexion\n");
printf{i in ND, j in Nv, k in K: i!=j} "    %3d         %3d       %8g        %3d\n",   i, j, k, c[i,j], x[i,j,k];
/*
printf "\n\nEl recorrido optimo tiene un coste %d\n\n",
   sum{(i,j) in E} c[i,j] * x[i,j];
printf("Nodo Origen   Nodo destino   Distancia   Orden nodo\n");
printf{(i,j) in E: x[i,j]} "    %3d         %3d       %8g           %3d\n",
   i, j, c[i,j], u[i];
*/
/*
printf("Nodo Origen   Nodo destino   Distancia   Orden nodo   Conexion\n");
printf{(i,j) in E: i!=j} "    %3d         %3d       %8g        %3d        %3d\n",
   i, j, c[i,j], u[i], x[i,j];
*/

# DATOS USADOS EN ESTE PROBLEMA ---------------
set Ntot_x_Ntot, within Ntot cross Ntot;
set Ntot_x_G within Ntot cross G;

# Los datos se encuentran en el fichero .dat
# data;


end;
