# This Python script generates a .dat file to test our program with random data.

import random
import numpy as np 


num_depositos = 3
num_clientes = 6
num_productos = 5
# num_vehiculos debe ser mayor o igual que num_depositos
num_vehiculos = 3

# MC la distancia maxima, que cada vehiculo se permite viajar
MC = 1500



distanc_max_entre_nodos = MC//2

min_fk_coste_fijo_vehic = MC//60
max_fk_coste_fijo_vehic = MC//50

max_demanda_por_producto = 50
min_size_compartimento = max_demanda_por_producto * 2
max_size_compartimento = max_demanda_por_producto * 3


# ----------- Fin de la parametrizacion -----------
print('INICIO: Se está creando el fichero datos.txt')
nodos_tot = num_depositos+num_clientes

# M Numero muy grande.
# En realidad basta con el numero de arcos + 1 = (num_depositos + num_clientes - 1)**2 + 1
# Pero se va a poner un poco mas.
M = (num_depositos + num_clientes + 1)**2


file = open('datos.txt','w')
distancia_aux = np.ndarray(shape=(nodos_tot+1,nodos_tot+1), dtype = int)




strAux = ('# Prueba. Fichero aleatorio' + 
          '\n# num_depositos = num_nodos - num_clientes ND')
file.write(strAux)
strAux = ('\nparam num_depositos := ' + str(num_depositos) + ';') 
file.write(strAux)

strAux = ('\n# num_clientes = num_nodos - num_depositos, Nv')
file.write(strAux)
strAux = ('\nparam num_clientes := ' + str(num_clientes) + ';')
file.write(strAux)

strAux = ('\n# G')
file.write(strAux)
strAux = ('\nparam num_productos := ' + str(num_productos) + ';')
file.write(strAux)

strAux = ('\n# K')
file.write(strAux)
strAux = ('\nparam num_vehiculos := ' + str(num_vehiculos) + ';')
file.write(strAux)

strAux = ('\n\n# MC la distancia maxima, que cada vehiculo se permite viajar')
file.write(strAux)
strAux = ('\nparam MC := ' + str(MC) + ';')
file.write(strAux)

strAux = ('\n\n# M un numero muy grande.' +
          '\n# En realidad basta con el (numero de arcos + 1) = (' + 
          str(num_depositos) + ' + '+ str(num_clientes) + ' - 1)^2 + 1.' + 
          '\n# Pero lo pongo un poco mas grande = (' +
          str(num_depositos) + ' + '+ str(num_clientes) + ' + 1)^2.')
file.write(strAux)
strAux = ('\nparam M := ' + str(M)  + ';')
file.write(strAux)




strAux = ('\n\n#c_ij la distancia entre los nodos i y j' +
          '\nparam : Ntot_x_Ntot : c :=')
file.write(strAux)
# print(strAux)

for i in range(1, nodos_tot+1):
    for j in range(1, nodos_tot+1):
        if i == j:
            distancia_aux[i,j] = 0
        elif i < j:
            distancia_aux[i,j] = random.randint(1, distanc_max_entre_nodos)
        else:
            distancia_aux[i,j] = distancia_aux[j, i]
            
        strAux = ('\n    ' + str(i) + '  ' + str(j) + '  ' + str(distancia_aux[i,j]))
        # print(strAux)
        file.write(strAux)
strAux = ('\n;')
file.write(strAux)



strAux = ('\n\n#d_ig demanda del nodo i para el producto g' +
         '\nparam : Nv_x_G : d :=')
file.write(strAux)
# print(strAux)

for i in range(num_depositos+1, nodos_tot+1):
    for j in range(1, num_productos+1):
        if (random.randint(0, 2) < 1):
            # Hacemos que la mitad de los productos demandados sean cero
            valor_aux = 0
        else:
            valor_aux = random.randint(1, max_demanda_por_producto)
            
        strAux = ('\n    ' + str(i) + '  ' + str(j) + '  ' + str(valor_aux))
        # print(strAux)
        file.write(strAux)
strAux = ('\n;')
file.write(strAux)


strAux = ('\n\n#Q_g la capacidad del compartimento del vehiculo dedicado al producto g' +
          '\n# param Q{g in G} :=' +
          '\nparam Q :=')
file.write(strAux)
# print(strAux)

for i in range(1, num_productos+1):
    num_compartimentos_aux = random.randint(min_size_compartimento, max_size_compartimento)
    strAux = ('\n    ' + str(i) + '  ' + str(num_compartimentos_aux) + 
              '    # En cualquier vehiculo hay '  + str(num_compartimentos_aux) +
              ' compartimentos para el producto ' + str(i))
    # print(strAux)
    file.write(strAux)
strAux = ('\n;')
file.write(strAux)



strAux = ('\n\n# DQ_ik la lista de vehiculos k que salen del deposito i')
file.write(strAux)
# print(strAux)
# Se ponen comentarios explicativos del estilo
#       1  1   1    # Indica que en el deposito 1, el vehiculos 1; SI esta disponible.
#       1  2   0    # Indica que en el deposito 1, el vehiculos 2; NO esta disponible.
strAux = ('\nparam : ND_x_K : DQ :=')
file.write(strAux)
# print(strAux)

# Se crea la lista de vehiculos por deposito
num_vehic_aux = np.zeros(shape=(num_depositos+1), dtype = int)
# print('num_vehic_aux.shape =', num_vehic_aux.shape)
# print('num_vehic_aux.sum() INI =', num_vehic_aux.sum())
num_depot_aux = 1

# Se crea la lista de vehiculos para todos los depositos excepto el ultimo
for n in range(1, num_depositos):
    num_vehic_aux[n] = random.randint(1, num_vehiculos//num_depositos)
    print('num_vehic_aux[', n, ']', num_vehic_aux[n])
    num_depot_aux += num_depot_aux

# Se rellena el ultimo deposito con los vehiclos que restan
num_vehic_aux[num_depositos] = num_vehiculos - num_vehic_aux.sum()
print('num_vehic_aux[', num_depositos, ']', num_vehic_aux[num_depositos])
print('num_vehic_aux.sum() FIN =', num_vehic_aux.sum())

offset_k = 0
for i in range(1, num_depositos+1):
    # Voy a poner los n vehiculos en el siguiente deposito
    # Se ponen los vehiculos que NO estan con un 0. Los del principio.
    for k in range(1, 1 + offset_k): 
        strAux = ('\n    ' + str(i) + '  '  + str(k) + '  0' + 
                  '    # Indica que en el deposito ' + str(i) + 
                  ' NO esta disponible vehiculo ' + str(k))
        # print('CEROS i = ', i, ', k = ', k)
        # print(strAux)
        file.write(strAux)
        
    # Se ponen los vehiculos que SI estan con un 1. Los del medio.
    for k in range(1 + offset_k, num_vehic_aux[i] + 1 + offset_k): 
        strAux = ('\n    ' + str(i) + '  '  + str(k) + '  1' + 
                  '    # Indica que en el deposito ' + str(i) + 
                  ' SI esta disponible vehiculo ' + str(k))
        # print('UNOS i = ', i, ', k = ', k)
        file.write(strAux)
    
    if ((num_vehic_aux[i] + 1 + offset_k) < (num_vehiculos + 1)):
        # Se ponen los vehiculos que NO estan con un 0. Los del final
        for k in range(num_vehic_aux[i] + 1 + offset_k, num_vehiculos + 1): 
            strAux = ('\n    ' + str(i) + '  '  + str(k) + '  0' + 
                      '    # Indica que en el deposito ' + str(i) + 
                      ' NO esta disponible vehiculo ' + str(k))
            # print('CEROS i = ', i, ', k = ', k)
            # print(strAux)
            file.write(strAux)
        
    offset_k += num_vehic_aux[i]
    print('offset_k =', offset_k)
strAux = ('\n;')
file.write(strAux)


strAux = ('\n\n# fk el costo fijo de usar el vehiculo k' +
          '\n# param : K : fk :=' +
          '\nparam fk :=')
file.write(strAux)
# print(strAux)

for i in range(1, num_vehiculos+1):
    strAux = ('\n    ' + str(i) + '  ' +
              str(random.randint(min_fk_coste_fijo_vehic, max_fk_coste_fijo_vehic)))
    # print(strAux)
    file.write(strAux)
strAux = ('\n;')
file.write(strAux)


# Print end of Gusek file
strAux = ('\nend;\n\n')
file.write(strAux)     


file.close()

print('FIN. Ya se ha creado el fichero datos.txt')
