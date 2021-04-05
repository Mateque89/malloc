/* Szymon Pielat 308859 Oświadczam że jestem jedynym autorem kodu źrodłowego,
W swoim roziązaniu wykorzystałem szkielet dostarczony przez prowadzącego.
W moim rozwiązaniu wykorzystałem:
-gorliwe złączanie wolnych bloków
-wyszukiwanie Best-Fit
-zoptymalizowane boundary tagi
-dwukierunkową listę wolnych bloków
według idei przedstawionych na wykładzie.

Opis bloków:
Bloki dzielimy na wolne i zajęte.

* Blok wolny składa sie z | Header | Prev | Next | Footer |
Header: Mowi nam o rozmiarze bloku, oraz tym że jest wolny
Prev: Jest to offset do poprzedniego wolnego bloku na liście
Next: Jest to offset do kolejnego wolnego bloku na liście
Header: Mowi nam o rozmiarze bloku, oraz tym że jest wolny

Między Next a Footerem może występować opcjonalny padding,
ale tym w wolnym bloku sie nie przejmujemy.

* Blok zajęty składa sie z | Header |       Payload       |
Header: Mowi nam o rozmiarze bloku, oraz czy jest zajęty,
oraz o dostępności poprzednika.
Payload: Udostępniany użytkownikowi.

Nowe bloki do listy wolnych bloków wstawiane są na początek
listy. Offset bloków w liście jest liczony względem początku
sterty.Offset NULL'owy określiłem jako 1 (przy obecnym początku
sterty nieosiągalny)

Wyznaczanie rozmiaru bloku:
Do rozmiaru bloku jaki rząda użytkownik my będziemy dodawać
sizeof(word_t) przeznaczony dla headera, następnie rozmiar
będziemy zaokrąglać w górę do pierwszej wielokrotności liczby 16.

Wysoko poziomowy opis działania:

Malloc:
Przy alokacji bloku rozpatrujemy 2 przypadki:
1. istnieje wolny blok którego rozmiar jest wystarczający,
więc w nim alokujemy dane, jeżeli znaleziony blok jest za duży to go dzielimy.

2. Nie znaleziono wolnego bloku którego rozmiar jest odpowieni,
rozszerzamy stertę, tworząc nowy blok.

Free:
(poprzednik - lewy sąsiadujący blok, następnik - prawy sąsiadujący blok)
Przy zwalnianiu bloku mamy 4 scenariusze:
1. Poprzednik oraz następnik są wolni, więc scalamy 3 bloki w 1 wolny.
2. Poprzednik jest wolny, więc sie z nim scalamy w 1 blok wolny.
3. Następnik  jest wolny, więc sie z nim scalamy w 1 blok wolny.
4. Zwalniamy blok bez scalania z poprzednikiem i następnikiem.

W przypadku scalania z innymi blokami, uprzednio usuwamy scalane bloki z
listy wolnych bloków, free doda nowy scalony blok do listy.

Realloc:
Rozpatrujemy 5 scenariuszy:
1. Rozmiar nie został podany, zachowanie free(ptr)
2. Wskaźnik nie został podany, zachowanie malloca(size)
3. Podany rozmiar jest taki sam dotychczasowy, nic nie robimy.
4. Podany rozmiar jest mniejszy niż dotychczasowy zmniejszamy blok, z zwolnionej
części tworzymy nowy wolny blok.
5. Podany rozmiar jest większy niż dotychczasowy, zwiększamy blok.
Przy zwiększaniu bloku mamy następujące podprzypadki:
5.1)Jeżeli blok ma wolnego następnika, oraz razem z nim nasz rozmiar jest
odpowieni scalamy się(unikamy kopiowania danych do nowego bloku).
5.2)Jeżeli blok ma wolnego poprzednika, oraz z nim nasz rozmiar jest
odpowiedni scalamy się, oraz kopiujemy dane(unikamy szukania nowego bloku).
5.3)Poprzednie podprzypadki nie zaszły, znajdujemy nowy blok, kopiujemy dane
zwalniamy stary blok.

*/

#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>
#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.
 * When you hand in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
#define debug(fmt, ...) printf("%s: " fmt "\n", __func__, __VA_ARGS__)
#define msg(...) printf(__VA_ARGS__)
#else
#define debug(fmt, ...)
#define msg(...)
#endif

#define __unused __attribute__((unused))
/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* !DRIVER */

#define NULL_OFFSET 1 /* Nieosiągalny przy obecnym początku sterty */

typedef int32_t word_t; /* Heap is bascially an array of 4-byte words. */

typedef enum {
  FREE = 0,     /* Block is free */
  USED = 1,     /* Block is used */
  PREVFREE = 2, /* Previous block is free (optimized boundary tags) */
} bt_flags;

static word_t *heap_start; /* Address of the first block */
static word_t *heap_end;   /* Address past last byte of last block */
static word_t *last;       /* Points at last block */
static word_t *list_start; /* Points at first free block */

/* --=[ boundary tag handling ]=-------------------------------------------- */

static inline word_t bt_size(word_t *bt) {
  return *bt & ~(USED | PREVFREE);
}

static inline int bt_used(word_t *bt) {
  return *bt & USED;
}

static inline int bt_free(word_t *bt) {
  return !(*bt & USED);
}

/* Given boundary tag address calculate it's buddy address. */
static inline word_t *bt_footer(word_t *bt) {
  return (void *)bt + bt_size(bt) - sizeof(word_t);
}

/* Given payload pointer returns an address of boundary tag. */
static inline word_t *bt_fromptr(void *ptr) {
  return (word_t *)ptr - 1;
}
/* Previous block free flag handling for optimized boundary tags. */
static inline bt_flags bt_get_prevfree(word_t *bt) {
  return *bt & PREVFREE;
}

static inline void bt_clr_prevfree(word_t *bt) {
  if (bt)
    *bt &= ~PREVFREE;
}

static inline void bt_set_prevfree(word_t *bt) {
  *bt |= PREVFREE;
}

/* Returns address of payload. */
static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}

static size_t round_up(size_t size) {
  return (size + ALIGNMENT - 1) & -ALIGNMENT;
}

/* Returns address of next block or NULL. */
static inline word_t *bt_next(word_t *bt) {
  if (bt == last) {
    return NULL;
  }

  return (void *)bt + bt_size(bt);
}

/* Returns address of previous block or NULL. */
static inline word_t *bt_prev(word_t *bt) {
  if (bt == heap_start) {
    return NULL;
  }
  word_t *footer = bt - 1;
  return (void *)footer - bt_size(footer) + sizeof(word_t);
}
/* Oblicza ile słow word_t znajduje sie dany blok od heap_start */
static inline word_t list_block_offset(word_t *bt) {
  return (word_t)(uint64_t)((void *)bt - (void *)heap_start);
}

static inline word_t *list_get_next(word_t *bt) {
  word_t offset = (word_t)((uint64_t) * (bt + 2));
  if (offset == NULL_OFFSET) {
    return NULL;
  }
  return (void *)heap_start + offset;
}

static inline word_t *list_get_prev(word_t *bt) {
  word_t offset = (word_t)((uint64_t) * (bt + 1));
  if (offset == NULL_OFFSET) {
    return NULL;
  }
  return (void *)heap_start + offset;
}

static inline void list_set_prev(word_t *bt, word_t offset) {
  word_t *prev = bt + 1;
  *prev = offset;
}

static inline void list_set_next(word_t *bt, word_t offset) {
  word_t *next = bt + 2;
  *next = offset;
}

static inline void list_add(word_t *bt) {
  if (!list_start) {
    list_set_next(bt, NULL_OFFSET);
    list_set_prev(bt, NULL_OFFSET);
    list_start = bt;
  } else {
    word_t offset_old_last = list_block_offset(list_start);
    word_t offset_new_last = list_block_offset(bt);
    list_set_next(bt, offset_old_last);
    list_set_prev(bt, NULL_OFFSET);
    list_set_prev(list_start, offset_new_last);
    list_start = bt;
  }
}

static inline void list_remove(word_t *bt) {
  word_t *curr = list_start;
  while (curr) {
    if (bt == curr) {
      word_t *prev = list_get_prev(curr);
      word_t *next = list_get_next(curr);
      if (prev && next) {
        word_t offset_to_next = list_block_offset(next);
        word_t offset_to_prev = list_block_offset(prev);
        list_set_next(prev, offset_to_next);
        list_set_prev(next, offset_to_prev);
      } else if (prev) {
        list_set_next(prev, NULL_OFFSET);
      } else if (next) {
        list_set_prev(next, NULL_OFFSET);
        list_start = next;
      } else {
        list_start = NULL;
      }
    }
    curr = list_get_next(curr);
  }
}

/* Creates boundary tag(s) for given block. */
static inline void bt_make(word_t *bt, size_t size, bt_flags flags) {
  *bt = size | flags;

  if ((void *)bt + size == heap_end) {
    last = bt;
  }
  if (flags == (bt_flags)USED) {
    word_t *next = bt_next(bt);
    bt_clr_prevfree(next);
  }
  if (flags == (bt_flags)FREE) {
    *bt_footer(bt) = size | flags;
    list_add(bt);
    word_t *next = bt_next(bt);
    if (next) {
      bt_set_prevfree(next);
    }
  }
}

/* --=[ miscellanous procedures ]=------------------------------------------ */

/* Calculates block size incl. header, footer & payload,
 * and aligns it to block boundary (ALIGNMENT). */
static inline size_t blksz(size_t size) {
  size_t reqsize = size + sizeof(word_t);
  return round_up(reqsize);
}

static void *morecore(size_t size) {
  void *ptr = mem_sbrk(size);
  if (ptr == (void *)-1)
    return NULL;
  return ptr;
}

void write_blocks() {
  word_t *curr = heap_start;
  msg("Heap start:%p, Heap end:%p, Last block:%p\n", heap_start, heap_end,
      last);
  while (curr) {
    size_t size = bt_size(curr);
    msg("Block_start:%p, Block_end:%p, Blok_size:%ld, Used:%d, Prev_free:%d\n",
        curr, (void *)curr + size, size, bt_used(curr), bt_get_prevfree(curr));
    curr = bt_next(curr);
    (void)size;
  }
  msg("\n\n");
}

void write_list() {
  word_t *curr = list_start;
  msg("Tu sie zaczyna lista:%p\n", curr);
  while (curr) {
    size_t size = bt_size(curr);
    msg("List_block:%p, List_block_end:%p, List_block_size:%ld\n", curr,
        (void *)curr + size, size);
    curr = list_get_next(curr);
    (void)size;
  }
  msg("\n\n");
}
/* --=[ mm_init ]=---------------------------------------------------------- */

int mm_init(void) {
  void *ptr = morecore(ALIGNMENT - sizeof(word_t));
  if (!ptr)
    return -1;
  heap_start = NULL;
  heap_end = NULL;
  last = NULL;
  list_start = NULL;
  return 0;
}

#if 0
/* First fit startegy. */
static word_t *find_fit(size_t reqsz) {
  word_t *curr = list_start;
  while (curr) {
    if (bt_size(curr) >= reqsz) {
      list_remove(curr);
      return curr;
    }
    curr = list_get_next(curr);
  }
  return NULL;
}
#else
/* Best fit startegy. */
static word_t *find_fit(size_t reqsz) {
  word_t *curr = list_start;
  word_t *best = NULL;
  size_t best_size = SIZE_MAX;
  while (curr) {
    size_t curr_size = bt_size(curr);
    if (curr_size >= reqsz) {
      if (curr_size == reqsz) {
        return curr;
      } else if (best_size > curr_size) {
        best = curr;
        best_size = curr_size;
      }
    }
    curr = list_get_next(curr);
  }
  return best;
}
#endif

/* --=[ malloc ]=----------------------------------------------------------- */

void *malloc(size_t size) {
  size_t block_size = blksz(size);
  size_t prev_was_free = 0;
  word_t *ptr = find_fit(block_size);

  if (!ptr) {
    ptr = mem_sbrk(block_size);
    if (!ptr) {
      return NULL;
    }
    if (!heap_start) {
      heap_start = ptr;
    }
    heap_end = (void *)ptr + block_size;
    if (last && bt_free(last)) {
      prev_was_free = 1;
    }
    last = ptr;
  } else {
    list_remove(ptr);
    size_t found_size = bt_size(ptr);
    word_t *next = bt_next(ptr);
    if (next) {
      bt_clr_prevfree(next);
    }
    if (found_size != block_size) {
      size_t free_size = found_size - block_size;
      word_t *second_half = (void *)ptr + block_size;
      bt_make(second_half, free_size, FREE);
    } else {
      block_size = found_size;
    }
  }

  bt_make(ptr, block_size, USED);
  if (prev_was_free) {
    bt_set_prevfree(ptr);
  }
  return bt_payload(ptr);
}
/* --=[ free ]=----------------------------------------------------------- */
void free(void *ptr) {
  if (!ptr) {
    return;
  }
  word_t *bt = bt_fromptr(ptr);
  size_t block_size = bt_size(bt);
  word_t *right = bt_next(bt);
  word_t *left = bt_get_prevfree(bt) ? bt_prev(bt) : NULL;

  if (left && right && bt_free(right)) {
    block_size = block_size + bt_size(left) + bt_size(right);
    bt = left;
    list_remove(left);
    list_remove(right);
  } else if (left) {
    block_size = block_size + bt_size(left);
    bt = left;
    list_remove(left);
  } else if (right && bt_free(right)) {
    list_remove(right);
    block_size = block_size + bt_size(right);
  }

  bt_make(bt, block_size, FREE);
}
/* --=[ realloc ]=----------------------------------------------------------- */
void *realloc(void *old_ptr, size_t size) {

  if (!old_ptr) {
    void *new_ptr = malloc(size);
    if (!new_ptr) {
      return NULL;
    }
    return new_ptr;
  }
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }
  size_t requested_size = blksz(size);
  word_t *bt = bt_fromptr(old_ptr);
  size_t old_size = bt_size(bt);
  if (requested_size == old_size) {
    return old_ptr;
  }

  if (requested_size < old_size) {
    size_t leftover_size = old_size - requested_size;
    word_t *leftover_start = (void *)bt + requested_size;
    size_t prev_was_free = bt_get_prevfree(bt) ? 1 : 0;
    bt_make(bt, requested_size, USED);
    if (prev_was_free) {
      bt_set_prevfree(bt);
    }
    bt_make(leftover_start, leftover_size, USED);
    free(bt_payload(leftover_start));
    return bt_payload(bt);
  } else {
    word_t *next = bt_next(bt);
    if (next && bt_free(next)) {
      size_t connected_size = bt_size(bt) + bt_size(next);
      if (connected_size >= requested_size) {
        list_remove(next);
        next = bt_next(next);
        if (next) {
          bt_clr_prevfree(next);
        }
        size_t prev_was_free = bt_get_prevfree(bt) ? 1 : 0;
        bt_make(bt, connected_size, USED);
        if (prev_was_free) {
          bt_set_prevfree(bt);
        }
        return bt_payload(bt);
      }
    } else if (bt == last && bt_get_prevfree(bt)) {
      word_t *prev = bt_prev(bt);
      size_t connected_size = bt_size(bt) + bt_size(prev);
      if (connected_size >= requested_size) {
        list_remove(prev);
        memcpy(prev, bt, bt_size(bt));
        bt = prev;
        size_t prev_was_free = bt_get_prevfree(prev) ? 1 : 0;
        bt_make(bt, connected_size, USED);
        if (prev_was_free) {
          bt_set_prevfree(bt);
        }
        return bt_payload(bt);
      }
    }
    void *ptr = malloc(requested_size);
    if (ptr) {
      size_t old_size = bt_size(bt) - sizeof(word_t);
      memcpy(ptr, old_ptr, old_size);
      free(old_ptr);
      return ptr;
    }
  }
  return NULL;
}

/* --=[ calloc ]=----------------------------------------------------------- */
void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);
  if (new_ptr)
    memset(new_ptr, 0, bytes);
  return new_ptr;
}
/* --=[ mm_cheackheap
 * ]=----------------------------------------------------------- */
void mm_checkheap(int verbose) {
  word_t *curr = heap_start;
  word_t *last = NULL;
  size_t free_amount_stack = 0;
  size_t free_amout_list = 0;
  while (curr) {
    if ((void *)bt_payload(curr) < (void *)curr) {
      msg("[Blok: %p] Wadliwa pozycja payloadu", curr);
    }
    if (bt_size(curr) % 16 != 0) {
      msg("[Blok: %p] Rozmiar bloku nie jest podzielny przez 16!\n", curr);
    }
    if ((long)bt_payload(curr) % 16 != 0) {
      msg("[Blok: %p] Adres payloadu nie jest podzielny przez 16\n", curr);
    }
    if (last && bt_free(last) && bt_free(curr)) {
      write_blocks();
      write_list();
      msg("[Blok: %p] Nie moga ze soba sasiadowac 2 bloki wolne\n", curr);
    }
    if (last && (void *)last + bt_size(last) != curr) {
      msg("[Blok: %p, Ciaglosc blokow nie jest zachowana\n", last);
    }
    if (bt_free(curr)) {
      free_amount_stack++;
    }
    last = curr;
    curr = bt_next(curr);
  }

  curr = list_start;
  while (curr) {
    if (!bt_free(curr)) {
      msg("[Blok: %p] Blok na liscie wolnych blokow nie jest wolny!\n", curr);
    }
    if (list_get_next(curr) == curr) {
      msg("[Blok: %p] Na liscie występuje zapętlenie!\n", curr);
      break;
    }
    free_amout_list++;
    curr = list_get_next(curr);
  }
  if (free_amout_list != free_amount_stack) {
    msg("Lista wolnych blokow sie nie zgadza co do ilosci! Lista:%ld, "
        "Stack:%ld\n",
        free_amout_list, free_amount_stack);
  }
}
