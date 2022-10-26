# Compiladores
Código para la materia Compiladores 2021 de [LCC](https://dcc.fceia.unr.edu.ar), [FCEIA](https://www.fceia.unr.edu.ar), [UNR](https://www.unr.edu.ar).

Este es el código a partir del cual los estudiantes empiezan a desarrollar un compilador.

Para fijar la versión de GHC y de los paquetes usaremos la herramienta [stack](https://docs.haskellstack.org/en/stable/README/).

Los pasos para instalar son:

```code
stack setup
stack build
```

Luego se puede ejecutar con 
```code
stack run
```
o cargar el entorno interactivo GHCi
```code
stack ghci

stack ghci src/TypeChecker.hs
```

También se pueden cargar archivos. Desde stack:
```code
stack run -- miprograma.fd4
```

En general, los argumentos a nuestro programa se escriben luego de `--`. Por ejemplo,
```code
% stack run -- --help
Compilador de FD4 de la materia Compiladores 2021

Usage: compiladores-exe [(-t|--typecheck) | (-i|--interactive)] [FILES...]
  Compilador de FD4

Available options:
  -t,--typecheck           Chequear tipos e imprimir el término
  -k,--interactiveCEK      Ejecutar interactivamente en la CEK
  -m,--bytecompile         Compilar a la BVM
  -r,--runVM               Ejecutar bytecode en la BVM
  -i,--interactive         Ejecutar en forma interactiva
  -c,--cc                  Compilar a código C
  -o,--optimize            Optimizar código
  -h,--help                Show this help text
```
