#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <errno.h>
#include <assert.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdint.h>
#include <inttypes.h>
#include <gc.h>
#include <wchar.h>
#include <locale.h>

#define FAST 1
#define TRACE 0

#define quit(...)							\
	do {								\
		fprintf(stderr, __VA_ARGS__);				\
		fprintf(stderr, "\n");					\
		fprintf(stderr, "errno = %d\n", errno);			\
		exit(1);						\
	} while (0)

#if TRACE && !FAST
 #define _trace(...)							\
	do {								\
		fprintf(stderr, "TRACE: ");				\
		fprintf(stderr, __VA_ARGS__);				\
		fprintf(stderr, "\n");					\
	} while (0)
#else
 #define _trace(s, ...)
#endif

#if FAST
 #undef assert
 #define assert(x)
 #define IF_FAST(x) x
 #define IF_SLOW(x)
#else
 #undef NDEBUG
 #define IF_FAST(x)
 #define IF_SLOW(x) x
#endif
#define SLOW !FAST

#define RETURN   1
#define CONST    2
#define ACCESS   3
#define FUNCTION 4
#define CALL     5
#define ADD      6
#define SUB      7
#define IFZ      8
#define FIX      9
#define STOP     10
#define SHIFT    11
#define DROP     12
#define PRINT    13
#define PRINTN   14
#define JUMP     15
#define TAILCALL 16

#define CHUNK 4096

/*
 * Un bytecode es un array de enteros, incluyendo tanto opcodes como
 * datos (e.g. constantes enteras). Para las operaciones simples se
 * recorre opcode a opcode operando en la pila. Las más interesantes
 * involucran saltos y la construcción de clausuras.
 */
typedef uint32_t *code;

/*
 * Un entorno es una lista enlazada de valores. Representan los valores
 * para cada variable de de Bruijn en el "término" que evaluamos.
 */
typedef struct env *env;

/*
 * Una clausura: un par compuesto de un entorno y un cuerpo, que es
 * simplemente un puntero a código, es decir simplemente una etiqueta.
 */
struct clo {
	env  clo_env;
	code clo_body;
};

/*
 * Los valores son o un entero, o una clausura. Notar que no hay una
 * etiqueta para distinguirlos: la máquina asume que el bytecode estaba
 * bien tipado, y usa el dato que espera tener. No se hace ningún tipo
 * de chequeo en runtime.
 */
union value {
	uint32_t i;
	struct clo clo;
};
typedef union value value;

/*
 * Entornos: listas enlazadas de valores. Notar la recursión mutua
 * entre las clausuras y los entornos: un entorno es una lista de
 * valores, que pueden ser clausuras; y cada clausura tiene un entorno.
 */
struct env {
	value v;
	struct env *next;
};

/*
 * Empuja un valor al entorno `e` y devuelve el entorno extendido.
 */
static inline env env_push(env e, value v)
{
	env new = GC_malloc(sizeof *new);
	new->v = v;
	new->next = e;
	return new;
}

#if SLOW
/*
 * Sólo para debugging: devuelve la longitud de un entorno.
 */
static int env_len(env e)
{
	int rc = 0;
	while (e) {
		e = e->next;
		rc++;
	}
	return rc;
}
#endif

void run(code init_c)
{
	/*
	 * La pila de valores de la máquina, alocada en memoria dinámica.
	 * La se agranda si está cerca de llenarse el buffer.
	 */
	int stack_size = CHUNK;
	value *stack = GC_malloc(CHUNK * sizeof stack[0]);
	if (!stack)
		quit("OOM stack");

	/* El estado de la máquina. Son 3 punteros, empezando con
	 * el programa inicial, y pila y entornos vacíos. */
	code c = init_c;
	value *s = stack;
	env e = NULL;

	/*
	 * Usando la pila como un verdadero C Hacker
	 * ==========================================
	 *
	 * El puntero `s` apunta siempre una (1) dirección más adelante
	 * del último elemento de la pila, o equivalentemente a la primera
	 * dirección libre. Esto significa que podemos acceder al último
	 * elemento, en la cima de la pila, con s[-1]. El anteúltimo elemento
	 * está en s[-2].
	 *
	 * Para pushear un valor v a la pila hacemos:
	 *
	 *   *s++ = v;
	 *
	 * Esto es igual a *s = v; s = s + 1. Simétricamente,
	 * para sacar un valor de la pila, hacemos:
	 *
	 *   v = *--s;
	 *
	 * Que es igual a s = s - 1; v = *s
	 */

	while (1) {
		/*
		 * Agrandamos la pila si estamos cerca (a 10 elementos) de
		 * llenarla. Le agregamos otro bloque de CHUNK valores al final.
		 */
		if (s - stack > stack_size - 10) {
			int offset = s - stack;
			stack_size += CHUNK;
			value *new = GC_realloc (stack, stack_size * sizeof stack[0]);
			if (!new)
				quit("OOM stack grow");
			stack = new;
			s = stack + offset;
		}

		/* Tracing: sólo habilitado cuando compilamos
		 * en modo lento. */
		if (TRACE && !FAST) {
			code cc;
			printf("codes = [");
			for (cc = c; *cc != STOP; cc++) {
				printf("%2i ", *cc);
			}
			printf(" 10]\n");
		}
		_trace("c = %p", (void*)c);
		_trace("*c = %d", *c);
		_trace("|s| = %ld", s - stack);
		_trace("|e| = %d", env_len(e));

		/* Consumimos un opcode y lo inspeccionamos. A la vez,
		 * avanzamos el puntero de código. */
		switch(*c++) {
		case ACCESS: {
			/* Acceso a una variable: leemos el entero
			 * siguiente que representa el índice y recorremos
			 * el entorno hasta llegar a su binding. */
			int i = *c++;
			env ee = e;
			while (i--)
				ee = ee->next;

			/* Lo ponemos en la pila */
			*s++ = ee->v;
			break;
		}

		case CONST: {
			/* Una constante: la leemos y la ponemos en la pila */
			(*s++).i = *c++;
			break;
		}

		case ADD: {
			/* Suma: ya tenemos los valores en el tope de la pila,
			   la sumamos y la volvemos a poner en la pila */
			uint32_t y = (*--s).i;
			uint32_t x = (*--s).i;
			(*s++).i = x+y;
			break;
		}

  		case SUB: {
			/* resta: ya tenemos los valores en el tope de la pila,
			   hacemos la resta solo si x > y, sino es 0. */
			uint32_t y = (*--s).i;
			uint32_t x = (*--s).i;
			(*s++).i = x > y ? x-y : 0;
			break;
		}

		case RETURN: {
			/* Return: tenemos en la pila un valor y una dirección,
			 * y entorno, de retorno. Saltamos a la dirección
			 * de retorno y a su entorno, pero dejamos el valor
			 * de retorno en la pila. */
			value rv = *--s;

			struct clo ret_addr = (*--s).clo;

			e = ret_addr.clo_env;
			c = ret_addr.clo_body;

			*s++ = rv;
			break;
		}

		case CALL: {
			/* Aplicación: tenemos en la pila un argumento
			 * y una función. La función debe ser una clausura.
			 * La idea es saltar a la clausura extendiendo su
			 * entorno con el valor de la aplicación, pero
			 * tenemos que guardar nuestra dirección de retorno.
			 */
			value arg = *--s;
			value fun = *--s;

			struct clo ret_addr = { .clo_env = e, .clo_body = c };
			(*s++).clo = ret_addr;

			/* Cambiamos al entorno de la clausura, agregando arg */
			e = env_push(fun.clo.clo_env, arg);

			/* Saltamos! */
			c = fun.clo.clo_body;

			break;
		}


		case TAILCALL: {
			value arg = *--s;   // Tomamos el primer elemento del stack (argumento de la llamada)
			value fun = *--s;   // Tomamos la clausura de la funcion en pos de cola
			c = fun.clo.clo_body;	// Saltamos a la funcion
			e = env_push(fun.clo.clo_env, arg);	// Insertamos su entorno
			break;
		}

		/* Para IFZ leemos el primer valor del stack. Dependiendo
		 * si es o no 0 dependera el salto.
		*/
		case IFZ: {
			value cond = *(--s); 	// Extraemos el primer valor del stack
								// y corremode un lugar la referencia
			if (cond.i) { 		// Esto va a ser true si cond.i es
								// distinto de 0... cosas de la vida
				int len_branch_1 = *c++;  // Accedemos al tamaño de la rama verdadera.
				c += len_branch_1; 		  // Saltamos hasta la rama falsa.
			} else {
				c++;			// Ignoramos el tamaño de la verdadera y procedemos
								//  con la ejecucion.
			}

			break;
        }
        
		case JUMP: {
			int offset = *c++;
			c += offset;
			break;
		}

		case FUNCTION: {
			/* Un lambda, es un valor! Armamos una clausura
			 * la ponemos en la pila, y listo! */

			/*
			 * La parte tramposa es que el cuerpo del lambda
			 * puede tener cualquier longitud y tenemos que saber
			 * donde seguir evaluando. Nuestro bytecode
			 * incluye la longitud del cuerpo del lambda en
			 * el entero siguiente, así que lo consumimos.
			 */
			int leng = *c++;

			/* Ahora sí, armamos la clausura */
			struct clo clo = {
				.clo_env = e,
				.clo_body = c,
			};

			/* La ponemos en la pila */
			(*s++).clo = clo;

			/* Y saltamos todo el cuerpo del lambda */
			c += leng;

			break;
		}

		case FIX: {
			/*
			 * Fixpoint: algo de magia. Tenemos una clausura en
			 * la pila, donde su primer variable libre es el
			 * binding recursivo. La modificamos para que el
			 * entorno se apunte a sí mismo.
			 */
			value clo = *--s;
			env env_fix;

			/* Atar el nudo! */
			env_fix = env_push(e, clo);
			(clo.clo).clo_env = env_fix;
			env_fix->v = clo;

			(*s++) = clo;

			break;
		}

		case STOP: {
			return;
		}

		case SHIFT: {
			value v = *--s;
			e = env_push(e, v);
			break;
		}

		case DROP: {
			e = e->next;
			break;
		}

		case PRINTN: {
			uint32_t i = s[-1].i;
			wprintf(L"%" PRIu32 "\n", i);
			break;
		}

		case PRINT: {
		  	while(*c) {
		   		wchar_t x = *c++;
		   		putwchar(x);
		  	}
		  	c++;
		  	break;
		}

		default:
			quit("FATAL: unhandled op code, %d", *(c-1));
		}
	}
}

/*
 * main simplemente llama al intérprete sobre el código que hay en el
 * archivo argv[1]. Para ser más piolas, en vez de hacer malloc, leer
 * el código del archivo a ese buffer y saltar ahí, usamos memory
 * mapping. Le decimos al kernel que nos dé un puntero a los contenidos
 * del archivo, y se leen automáticamente a medida que se necesitan.
 * Si el bytecode fuera realmente grande, esta laziness puede ser
 * conveniente.
 */
int main(int argc, char **argv)
{
	code codeptr;
	int fd;
	struct stat sb;

	setlocale(LC_ALL,"");

	if (argc < 2)
		quit("I need a filename");

	fd = open(argv[1], O_RDONLY);
	if (fd < 0)
		quit("open");

	/* Para obtener el tamaño del archivo. */
	if (fstat(fd, &sb) < 0)
		quit("fstat");

	/* Mapeamos el archivo */
	codeptr = mmap(NULL, sb.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
	if (!codeptr)
		quit("mmap");

	/* Llamamos a la máquina */
	run(codeptr);

	return 0;
}
