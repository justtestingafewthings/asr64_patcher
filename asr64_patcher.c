#define _POSIX_C_SOURCE 200809L
#include <fcntl.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

struct section {
  uint64_t address;
  size_t offset, length;
};
struct function {
  size_t begin, end;
  int thumb;
};
struct image {
  uint32_t cpu, subtype;
  struct section text, strings;
  uint64_t base;
  size_t functions, functions_length;
  int have_functions;
  struct function *bounds;
  size_t nfunctions;
};
static uint16_t le16(const unsigned char *p) {
  return (uint16_t)p[0] | (uint16_t)p[1] << 8;
}
static uint32_t le32(const unsigned char *p) {
  return (uint32_t)p[0] | (uint32_t)p[1] << 8 | (uint32_t)p[2] << 16 |
         (uint32_t)p[3] << 24;
}
static uint64_t le64(const unsigned char *p) {
  return le32(p) | (uint64_t)le32(p + 4) << 32;
}
static void put32(unsigned char *p, uint32_t v) {
  for (unsigned i = 0; i < 4; ++i)
    p[i] = (unsigned char)(v >> (8 * i));
}
static int range(size_t off, uint64_t count, size_t length) {
  return off <= length && count <= length - off;
}
static int error(const char *message) {
  fprintf(stderr, "asr64_patcher: %s\n", message);
  return -1;
}

static int parse(const unsigned char *b, size_t n, struct image *im) {
  if (n < 28)
    return error("truncated Mach-O header");
  int wide = le32(b) == 0xfeedfacf;
  if (!wide && le32(b) != 0xfeedface)
    return error("expected a thin little-endian Mach-O");
  size_t head = wide ? 32 : 28;
  if (n < head || le32(b + 12) != 2)
    return error("expected a Mach-O executable");
  im->cpu = le32(b + 4);
  im->subtype = le32(b + 8);
  if ((wide && (im->cpu != 0x100000c || (im->subtype & 0xffffff) > 2)) ||
      (!wide && (im->cpu != 12 ||
                 (im->subtype != 9 && im->subtype != 11 && im->subtype != 12))))
    return error(
        "unsupported architecture, expected ARM64, ARMv7, ARMv7s or ARMv7k");
  uint32_t commands = le32(b + 16), bytes = le32(b + 20);
  if (!range(head, bytes, n) || commands > bytes / 8)
    return error("invalid load-command bounds");
  size_t end = head + bytes, p = head;
  unsigned texts = 0, strings = 0;
  for (uint32_t i = 0; i < commands; ++i) {
    if (!range(p, 8, end))
      return error("truncated load command");
    uint32_t cmd = le32(b + p), size = le32(b + p + 4);
    if (size < 8 || size % 4 || !range(p, size, end))
      return error("invalid load command size");
    if (cmd == 0x26) {
      if (size != 16 || im->have_functions ||
          !range(le32(b + p + 8), le32(b + p + 12), n))
        return error("invalid function starts");
      im->have_functions = 1;
      im->functions = le32(b + p + 8);
      im->functions_length = le32(b + p + 12);
    }
    if (cmd == (wide ? 0x19u : 1u)) {
      size_t fixed = wide ? 72 : 56, step = wide ? 80 : 68;
      if (size < fixed)
        return error("truncated segment");
      uint64_t vm = wide ? le64(b + p + 24) : le32(b + p + 24),
               vs = wide ? le64(b + p + 32) : le32(b + p + 28);
      uint64_t fo = wide ? le64(b + p + 40) : le32(b + p + 32),
               fs = wide ? le64(b + p + 48) : le32(b + p + 36);
      if (!memcmp(b + p + 8, "__TEXT\0", 7))
        im->base = vm;
      uint32_t count = le32(b + p + (wide ? 64 : 48));
      if (fo > n || fs > n - fo || vs < fs || vm > UINT64_MAX - vs ||
          count > (size - fixed) / step)
        return error("invalid segment bounds");
      for (uint32_t j = 0; j < count; ++j) {
        size_t s = p + fixed + j * step;
        uint64_t a = wide ? le64(b + s + 32) : le32(b + s + 32),
                 len = wide ? le64(b + s + 40) : le32(b + s + 36);
        size_t off = le32(b + s + (wide ? 48 : 40));
        uint32_t flags = le32(b + s + (wide ? 64 : 56));
        if (a < vm || a - vm > vs || len > vs - (a - vm))
          return error("invalid section address");
        unsigned type = flags & 255;
        if (type != 1 && type != 12 && type != 18 &&
            (!range(off, len, n) || off < fo || off - fo > fs ||
             len > fs - (off - fo)))
          return error("invalid section file bounds");
        struct section section = {a, off, (size_t)len};
        if (!memcmp(b + s, "__text\0", 7) &&
            !memcmp(b + s + 16, "__TEXT\0", 7)) {
          if (type != 0 || !(flags & 0x80000000u) ||
              !(le32(b + p + (wide ? 60 : 44)) & 4))
            return error("text section is not executable");
          im->text = section;
          ++texts;
        }
        if (!memcmp(b + s, "__cstring\0", 10) &&
            !memcmp(b + s + 16, "__TEXT\0", 7)) {
          if (type != 2)
            return error("invalid string section type");
          im->strings = section;
          ++strings;
        }
      }
    }
    p += size;
  }
  if (p != end || texts != 1 || strings != 1 || !im->text.length ||
      !im->strings.length)
    return error("missing or ambiguous text/string sections");
  if (wide &&
      (im->text.address % 4 || im->text.offset % 4 || im->text.length % 4))
    return error("unaligned ARM64 text");
  return 0;
}
/* Old ARMv7 binaries lack LC_FUNCTION_STARTS. */
static int thumb_prologue(const unsigned char *code, size_t p, size_t end) {
  if (end - p < 4)
    return 0;
  unsigned push = le16(code + p), registers = push & 255, count = 0;
  if ((push & 0xff80) != 0xb580)
    return 0;
  for (; registers; registers >>= 1)
    count += registers & 1;
  return le16(code + p + 2) == (0xaf00 | (count - 1));
}
static int legacy_function_starts(const unsigned char *b, struct image *im) {
  if (im->cpu != 12 || im->subtype != 9 || im->text.address % 2 ||
      im->text.offset % 2 || im->text.length % 2)
    return error("missing function starts");
  const unsigned char *code = b + im->text.offset;
  size_t count = 0;
  for (size_t p = 0; p < im->text.length; p += 2)
    count += thumb_prologue(code, p, im->text.length);
  if (!count || count > SIZE_MAX / sizeof(*im->bounds))
    return error("missing Thumb function prologues");
  im->bounds = calloc(count, sizeof(*im->bounds));
  if (!im->bounds)
    return error("out of memory");
  for (size_t p = 0; p < im->text.length; p += 2) {
    if (!thumb_prologue(code, p, im->text.length))
      continue;
    if (im->nfunctions)
      im->bounds[im->nfunctions - 1].end = p;
    im->bounds[im->nfunctions++] = (struct function){p, im->text.length, 1};
  }
  return 0;
}
static int function_starts(const unsigned char *b, struct image *im) {
  if (!im->have_functions)
    return legacy_function_starts(b, im);
  if (!im->functions_length)
    return error("missing function starts");
  uint64_t address = im->base, delta = 0;
  size_t capacity = 0;
  unsigned shift = 0;
  int terminated = 0;
  for (size_t i = 0; i < im->functions_length; ++i) {
    unsigned byte = b[im->functions + i];
    if (terminated) {
      if (byte)
        return error("nonzero function-start padding");
      continue;
    }
    if (shift >= 63 || (uint64_t)(byte & 127) > (UINT64_MAX >> shift))
      return error("invalid function-start delta");
    delta |= (uint64_t)(byte & 127) << shift;
    if (byte & 128) {
      shift += 7;
      continue;
    }
    if (!delta) {
      terminated = 1;
      continue;
    }
    if (address > UINT64_MAX - delta)
      return error("function-start overflow");
    address += delta;
    uint64_t pc = im->cpu == 12 ? address & ~UINT64_C(1) : address;
    if (pc < im->text.address || pc - im->text.address >= im->text.length ||
        pc % (im->cpu == 12 ? 2 : 4))
      return error("invalid function boundary");
    size_t begin = (size_t)(pc - im->text.address);
    if (im->nfunctions) {
      struct function *previous = &im->bounds[im->nfunctions - 1];
      if (begin <= previous->begin)
        return error("unordered function starts");
      previous->end = begin;
    }
    if (im->nfunctions == capacity) {
      size_t next = capacity ? capacity * 2 : 64;
      if (next > im->functions_length)
        next = im->functions_length;
      if (next > SIZE_MAX / sizeof(*im->bounds))
        return error("too many function starts");
      struct function *bounds = realloc(im->bounds, next * sizeof(*bounds));
      if (!bounds)
        return error("out of memory");
      im->bounds = bounds;
      capacity = next;
    }
    im->bounds[im->nfunctions++] =
        (struct function){begin, im->text.length, (address & 1) != 0};
    shift = 0;
    delta = 0;
  }
  if (!terminated || !im->nfunctions)
    return error("missing or unterminated function starts");
  return 0;
}
static const struct function *function_at(const struct image *im, size_t site) {
  size_t lo = 0, hi = im->nfunctions;
  while (lo < hi) {
    size_t mid = lo + (hi - lo) / 2;
    const struct function *f = &im->bounds[mid];
    if (site < f->begin)
      hi = mid;
    else if (site >= f->end)
      lo = mid + 1;
    else
      return f;
  }
  return NULL;
}
static int64_t sx(uint64_t x, unsigned bits) {
  return (int64_t)(x ^ (UINT64_C(1) << (bits - 1))) -
         (int64_t)(UINT64_C(1) << (bits - 1));
}
static int literal(const unsigned char *b, const struct section *s,
                   const char *str, uint64_t *address) {
  size_t len = strlen(str) + 1, found = 0;
  if (len > s->length)
    return error("missing signature diagnostic");
  for (size_t i = 0; i <= s->length - len; ++i)
    if ((i == 0 || b[s->offset + i - 1] == 0) &&
        !memcmp(b + s->offset + i, str, len - 1) &&
        (b[s->offset + i + len - 1] == 0 ||
         (i + len < s->length && b[s->offset + i + len - 1] == '.' &&
          b[s->offset + i + len] == 0))) {
      *address = s->address + i;
      ++found;
    }
  return found == 1 ? 0 : error("missing or ambiguous signature diagnostic");
}
static size_t thumb_size(const unsigned char *code, size_t p) {
  return (le16(code + p) >> 11) >= 29 ? 4 : 2;
}
static unsigned thumb_imm16(const unsigned char *code) {
  unsigned a = le16(code), b = le16(code + 2);
  return ((a & 15) << 12) | (((a >> 10) & 1) << 11) | (((b >> 12) & 7) << 8) |
         (b & 255);
}
static int thumb_call(const unsigned char *code, size_t p, size_t end) {
  return end - p >= 4 && (le16(code + p) & 0xf800) == 0xf000 &&
         (le16(code + p + 2) & 0xc000) == 0xc000;
}
static int thumb_branch(const unsigned char *code, size_t p, size_t end,
                        int64_t *target, int *condition) {
  unsigned a = le16(code + p), b = end - p >= 4 ? le16(code + p + 2) : 0;
  int64_t delta;
  *condition = -1;
  if ((a & 0xf800) == 0xe000) {
    delta = sx((a & 0x7ff) << 1, 12);
  } else if ((a & 0xf000) == 0xd000 && ((a >> 8) & 15) < 14) {
    *condition = (a >> 8) & 15;
    delta = sx((a & 255) << 1, 9);
  } else if ((a & 0xf500) == 0xb100) {
    *condition = 16 + ((a >> 11) & 1);
    delta = (((a >> 9) & 1) << 6) | (((a >> 3) & 31) << 1);
  } else if ((a & 0xf800) == 0xf000 && (b & 0xd000) == 0x8000 &&
             ((a >> 6) & 15) < 14) {
    *condition = (a >> 6) & 15;
    delta =
        sx((((a >> 10) & 1) << 20) | (((b >> 11) & 1) << 19) |
               (((b >> 13) & 1) << 18) | ((a & 63) << 12) | ((b & 0x7ff) << 1),
           21);
  } else if ((a & 0xf800) == 0xf000 && (b & 0xd000) == 0x9000) {
    unsigned s = (a >> 10) & 1;
    delta = sx((s << 24) | ((1 ^ ((b >> 13) & 1) ^ s) << 23) |
                   ((1 ^ ((b >> 11) & 1) ^ s) << 22) | ((a & 0x3ff) << 12) |
                   ((b & 0x7ff) << 1),
               25);
  } else {
    return 0;
  }
  *target = (int64_t)p + 4 + delta;
  return 1;
}
static int thumb_string(const unsigned char *code, size_t p, size_t end,
                        uint64_t vm, uint64_t string) {
  if (end - p >= 4 && (le16(code + p) & 0xff00) == 0x4800 &&
      le16(code + p + 2) == 0x4478) {
    uint64_t pool = ((vm + p + 4) & ~UINT64_C(3)) + (le16(code + p) & 255) * 4;
    if (pool >= vm && pool - vm <= end && end - (size_t)(pool - vm) >= 4)
      return (uint32_t)(vm + p + 6 + le32(code + (size_t)(pool - vm))) ==
             string;
  }
  if (end - p < 10)
    return 0;
  if ((le16(code + p) & 0xfbf0) != 0xf240 || (le16(code + p + 2) & 0x8f00) ||
      (le16(code + p + 4) & 0xfbf0) != 0xf2c0 ||
      (le16(code + p + 6) & 0x8f00) || le16(code + p + 8) != 0x4478)
    return 0;
  uint32_t value = thumb_imm16(code + p) | (thumb_imm16(code + p + 4) << 16);
  return (uint32_t)(vm + p + 12 + value) == string;
}
static int thumb_reaches(const unsigned char *code, size_t begin, size_t end,
                         unsigned char *boundary, size_t start, size_t goal) {
  size_t pending[128], head = 0, tail = 0;
  for (size_t i = 0; i < end - begin; ++i)
    boundary[i] &= (unsigned char)~2u;
  pending[tail++] = start;
  while (head < tail) {
    size_t p = pending[head++];
    if (p < begin || p >= end || !(boundary[p - begin] & 1) ||
        (boundary[p - begin] & 4))
      return 0;
    if (boundary[p - begin] & 2)
      continue;
    boundary[p - begin] |= 2;
    if (p == goal)
      return 1;
    unsigned op = le16(code + p);
    if (thumb_call(code, p, end) || (op & 0xff00) == 0x4700 ||
        (op & 0xff00) == 0xbd00)
      continue;
    int condition;
    int64_t target;
    size_t next = p + thumb_size(code, p);
    if (tail + 2 > sizeof(pending) / sizeof(pending[0]))
      return 0;
    if (thumb_branch(code, p, end, &target, &condition)) {
      if (target < (int64_t)begin || target >= (int64_t)end)
        return 0;
      pending[tail++] = (size_t)target;
      if (condition == -1)
        continue;
    }
    if (next < end)
      pending[tail++] = next;
  }
  return 0;
}
struct thumb_patch {
  size_t site;
  uint32_t replacement;
  int patched;
};
static int thumb_jump(size_t site, size_t target, uint32_t *replacement) {
  int64_t delta = (int64_t)target - (int64_t)site - 4;
  if (delta % 2 || delta < -(INT64_C(1) << 24) || delta >= (INT64_C(1) << 24))
    return 0;
  uint32_t d = (uint32_t)delta, s = (d >> 24) & 1;
  *replacement = 0xf000u | (s << 10) | ((d >> 12) & 0x3ff) |
                 ((0x9000u | ((1 ^ ((d >> 23) & 1) ^ s) << 13) |
                   ((1 ^ ((d >> 22) & 1) ^ s) << 11) | ((d >> 1) & 0x7ff))
                  << 16);
  return 1;
}
static int watch_candidate(const unsigned char *code, size_t begin, size_t end,
                           unsigned char *boundary, size_t p, size_t fail,
                           size_t pass, struct thumb_patch *patch) {
  if (p - begin < 10 || end - p < 24 || (boundary[p - begin] & 4) ||
      (le16(code + p) & 0xfbf0) != 0xf200 ||
      (le16(code + p + 2) & 0x8f00) != 0x0100)
    return 0;
  unsigned base = le16(code + p) & 15;
  unsigned field = (((le16(code + p) >> 10) & 1) << 11) |
                   (((le16(code + p + 2) >> 12) & 7) << 8) |
                   (le16(code + p + 2) & 255);
  size_t q = p + 4;
  if (base >= 13 || (le16(code + q) & 0xff00) != 0xa800)
    return 0;
  q += 2;
  int legacy = (le16(code + q) & 0xff00) == 0x2200;
  if (legacy) {
    if (!(le16(code + q) & 255))
      return 0;
    q += 2;
  }
  if (!thumb_call(code, q, end))
    return 0;
  q += 4;
  unsigned reload = 0;
  if ((le16(code + q) & 0xf800) == 0x9800 && (le16(code + q) & 0x0700)) {
    reload = le16(code + q);
    q += 2;
  }
  if (le16(code + q) != 0x2800)
    return 0;
  q += 2;
  int condition;
  int64_t target;
  if (!thumb_branch(code, q, end, &target, &condition) || condition != 1 ||
      !thumb_reaches(code, begin, end, boundary, (size_t)target, fail))
    return 0;
  q += thumb_size(code, q);
  size_t success = q;
  if (thumb_branch(code, q, end, &target, &condition) && condition == -1) {
    if (target < (int64_t)begin || target >= (int64_t)end)
      return 0;
    success = (size_t)target;
  }
  if (!thumb_reaches(code, begin, end, boundary, success, pass) ||
      field < (legacy ? 1u : 4u))
    return 0;
  uint32_t original =
      (legacy ? 0xf890u : 0xf8d0u) | base |
      ((uint32_t)((legacy ? 0 : 0x2000) | (field - (legacy ? 1 : 4))) << 16);
  for (size_t gap = 6; gap <= 10; gap += 2) {
    size_t site = p - gap, guard = site + 4;
    unsigned reg = legacy ? 0 : 2, op = le16(code + guard);
    if (!(boundary[site - begin] & 1) || (boundary[site - begin] & 4) ||
        !(boundary[guard - begin] & 1))
      continue;
    int finalized = 0;
    for (size_t back = 6; back <= 8 && site - begin >= back; back += 2) {
      size_t line = site - back;
      unsigned extra = le16(code + site - 2);
      if ((boundary[line - begin] & 1) && le16(code + line) == 0x200a &&
          thumb_call(code, line + 2, end) &&
          (back == 6 || (extra & 0xf800) == 0x9800 ||
           (extra & 0xff00) == 0x4600))
        finalized = 1;
    }
    if (!finalized)
      continue;
    if ((op & 0xf500) == 0xb100 && !(op & 0x0800) && (op & 7) == reg) {
      if (guard + 2 != p)
        continue;
    } else {
      if (op != (0x2800 | (reg << 8)))
        continue;
      guard += 2;
      if (!thumb_branch(code, guard, end, &target, &condition) ||
          condition != 0 || guard + thumb_size(code, guard) != p)
        continue;
    }
    if (!thumb_branch(code, guard, end, &target, &condition) ||
        target < (int64_t)q || target == (int64_t)success ||
        target >= (int64_t)end || !(boundary[(size_t)target - begin] & 1))
      continue;
    uint32_t replacement;
    if (reload) {
      int64_t delta = (int64_t)success - (int64_t)site - 6;
      if (delta % 2 || delta < -2048 || delta > 2046)
        continue;
      replacement =
          reload | ((0xe000u | ((uint32_t)(delta / 2) & 0x7ff)) << 16);
    } else {
      if (!thumb_jump(site, success, &replacement))
        continue;
    }
    uint32_t current = le32(code + site);
    if (current != original && current != replacement)
      continue;
    patch->site = site;
    patch->replacement = replacement;
    patch->patched = current == replacement;
    return 1;
  }
  return 0;
}
static int thumb_boundaries(const unsigned char *code, size_t begin, size_t end,
                            unsigned char *boundary) {
  unsigned it = 0;
  for (size_t p = begin; p < end;) {
    if (end - p < 2)
      return 0;
    size_t length = thumb_size(code, p);
    if (end - p < length)
      return 0;
    boundary[p - begin] = 1 | (it ? 4 : 0);
    if (it)
      --it;
    unsigned op = le16(code + p), mask = op & 15;
    if ((op & 0xff00) == 0xbf00 && mask) {
      it = 4;
      while (!(mask & 1)) {
        --it;
        mask >>= 1;
      }
    }
    p += length;
  }
  return 1;
}
static int watch_function(const unsigned char *code, const struct section *text,
                          size_t begin, size_t end, uint64_t failed,
                          uint64_t passed, size_t *failure_function,
                          struct thumb_patch *patch) {
  unsigned char *boundary = calloc(end - begin, 1);
  if (!boundary)
    return error("out of memory");
  size_t fail = 0, pass = 0, nf = 0, np = 0;
  if (!thumb_boundaries(code, begin, end, boundary)) {
    free(boundary);
    return 0;
  }
  for (size_t p = begin; p < end; p += thumb_size(code, p)) {
    if (thumb_string(code, p, end, text->address, failed)) {
      fail = p;
      ++nf;
    }
    if (passed && thumb_string(code, p, end, text->address, passed)) {
      pass = p;
      ++np;
    }
  }
  if (!passed) {
    if (nf)
      *failure_function = begin;
    free(boundary);
    return (int)nf;
  }
  if (!nf && np == 1) {
    for (size_t p = begin; p < end; p += thumb_size(code, p)) {
      if (!thumb_call(code, p, end) || (le16(code + p + 2) & 0xd000) != 0xd000)
        continue;
      unsigned a = le16(code + p), b = le16(code + p + 2), sign = (a >> 10) & 1;
      int64_t target = (int64_t)p + 4 +
                       sx((sign << 24) | ((1 ^ ((b >> 13) & 1) ^ sign) << 23) |
                              ((1 ^ ((b >> 11) & 1) ^ sign) << 22) |
                              ((a & 0x3ff) << 12) | ((b & 0x7ff) << 1),
                          25);
      if (target == (int64_t)*failure_function) {
        fail = p;
        ++nf;
      }
    }
  }
  int count = 0;
  if (nf == 1 && np == 1) {
    for (size_t p = begin; p < end; p += thumb_size(code, p))
      count +=
          watch_candidate(code, begin, end, boundary, p, fail, pass, patch);
  }
  free(boundary);
  return count;
}
static int watch(unsigned char *b, const struct image *im) {
  uint64_t failed = 0, passed = 0;
  if (literal(b, &im->strings, "Image failed signature verification",
              &failed) ||
      literal(b, &im->strings, "Image passed signature verification", &passed))
    return -1;
  if (!im->functions_length || im->text.address % 2 || im->text.length % 2)
    return error("missing function starts or unaligned ARMv7k text");
  const unsigned char *code = b + im->text.offset;
  size_t failure_function = 0;
  int count = 0;
  struct thumb_patch patch = {0};
  for (int round = 0; round < 2; ++round) {
    count = 0;
    for (size_t i = 0; i < im->nfunctions; ++i) {
      const struct function *f = &im->bounds[i];
      if (!f->thumb)
        continue;
      int found = watch_function(code, &im->text, f->begin, f->end, failed,
                                 round ? passed : 0, &failure_function, &patch);
      if (found < 0)
        return -1;
      count += found;
    }
    if (count != 1)
      return error("unrecognized or ambiguous ARMv7k signature verification");
  }
  size_t site = im->text.offset + patch.site;
  printf("ARMv7k%s\n  file 0x%zx: %08" PRIx32 " -> %08" PRIx32 "\n",
         patch.patched ? " (already patched)" : "", site, le32(b + site),
         patch.replacement);
  put32(b + site, patch.replacement);
  return 0;
}

struct thumb_diagnostic {
  size_t site, call, width;
  uint32_t original;
  int64_t logger;
};
static int thumb_boundary(const unsigned char *boundary,
                          const struct function *f, size_t p) {
  return p >= f->begin && p < f->end && boundary[p - f->begin] == 1;
}
static int thumb_previous(const unsigned char *code,
                          const unsigned char *boundary,
                          const struct function *f, size_t p,
                          size_t *previous) {
  for (size_t length = 2; length <= 4; length += 2) {
    if (p - f->begin >= length && (boundary[p - length - f->begin] & 1) &&
        thumb_size(code, p - length) == length) {
      *previous = p - length;
      return 1;
    }
  }
  return 0;
}
static int64_t thumb_call_target(const unsigned char *code, uint64_t vm,
                                 size_t call) {
  unsigned first = le16(code + call), second = le16(code + call + 2),
           sign = (first >> 10) & 1;
  uint64_t pc = vm + call + 4;
  if (!(second & 0x1000))
    pc &= ~UINT64_C(3); /* BLX uses a word-aligned PC. */
  int64_t delta = sx((sign << 24) | ((1 ^ ((second >> 13) & 1) ^ sign) << 23) |
                         ((1 ^ ((second >> 11) & 1) ^ sign) << 22) |
                         ((first & 0x3ff) << 12) | ((second & 0x7ff) << 1),
                     25);
  return (int64_t)(pc - vm) + delta;
}
static int thumb_diagnostic(const unsigned char *code, uint64_t vm,
                            const struct function *f,
                            const unsigned char *boundary, size_t p,
                            uint64_t string, int failure,
                            struct thumb_diagnostic *diagnostic) {
  if (f->end - p < 14 || !thumb_boundary(boundary, f, p))
    return 0;
  size_t q = p + 4;
  unsigned op = le16(code + q);
  int unrelated = ((op >> 8) & 7) != 0;
  int status = failure && unrelated && (op & 0xf8ff) == 0x2050;
  if (status || (!failure && unrelated && (op & 0xf8ff) == 0x2001))
    q += 2;
  if (f->end - q < 10 || !thumb_boundary(boundary, f, q) ||
      (le16(code + q) & 0xfbf0) != 0xf2c0 || (le16(code + q + 2) & 0x8f00) ||
      !thumb_boundary(boundary, f, q + 4) || le16(code + q + 4) != 0x4478 ||
      !thumb_boundary(boundary, f, q + 6) || !thumb_call(code, q + 6, f->end))
    return 0;
  uint32_t value = (uint32_t)(string - (vm + q + 8));
  if (thumb_imm16(code + q) != value >> 16)
    return 0;
  unsigned low = value & 65535;
  uint32_t original = 0xf240u | ((low >> 12) & 15) | (((low >> 11) & 1) << 10) |
                      (((((low >> 8) & 7) << 12) | (low & 255)) << 16);
  int64_t target;
  int condition;
  if (le32(code + p) != original &&
      (!failure || !thumb_branch(code, p, f->end, &target, &condition) ||
       condition != -1 || thumb_size(code, p) != 4))
    return 0;
  size_t call = q + 6;
  if (failure && !status) {
    if (f->end - call < 6)
      return 0;
    unsigned first = le16(code + call + 4);
    int narrow = (first & 0xf8ff) == 0x2050;
    int wide = f->end - call >= 8 && first == 0xf04f &&
               (le16(code + call + 6) & 0xf0ff) == 0x0050;
    if (!narrow && !wide)
      return 0;
  }
  *diagnostic = (struct thumb_diagnostic){p, call, 4, original,
                                          thumb_call_target(code, vm, call)};
  return 1;
}
static int thumb_literal_diagnostic(const unsigned char *code, uint64_t vm,
                                    const struct function *f,
                                    const unsigned char *boundary, size_t p,
                                    uint64_t string, int failure,
                                    struct thumb_diagnostic *diagnostic) {
  if (f->end - p < 8 || !thumb_boundary(boundary, f, p))
    return 0;
  unsigned op = le16(code + p);
  size_t width = thumb_size(code, p);
  int patched = 0, condition;
  int64_t target;
  if ((op & 0xff00) != 0x4800 &&
      !(op == 0xf8df && !(le16(code + p + 2) & 0xf000))) {
    if (!failure || !thumb_branch(code, p, f->end, &target, &condition) ||
        condition != -1)
      return 0;
    patched = 1;
  }
  size_t call = p + width;
  int pic = le16(code + call) == 0x4478;
  if (pic)
    call += 2;
  if (!thumb_boundary(boundary, f, call) || !thumb_call(code, call, f->end))
    return 0;
  if (failure &&
      (f->end - call < 6 || (le16(code + call + 4) & 0xf8ff) != 0x2050))
    return 0;
  uint32_t value =
      pic ? (uint32_t)(string - (vm + p + width + 4)) : (uint32_t)string;
  uint64_t base = (vm + p + 4) & ~UINT64_C(3);
  size_t matches = 0;
  uint32_t original = 0;
  unsigned limit = width == 2 ? 1020 : 4095;
  for (unsigned imm = 0; imm <= limit; imm += 4) {
    uint64_t pool = base + imm;
    if (pool < vm + f->begin || pool > vm + f->end || vm + f->end - pool < 4 ||
        le32(code + (size_t)(pool - vm)) != value)
      continue;
    uint32_t load = width == 2
                        ? (le32(code + p) & 0xffff0000u) | 0x4800u | (imm / 4)
                        : 0xf8dfu | (imm << 16);
    if (!patched && le32(code + p) != load)
      continue;
    original = load;
    ++matches;
  }
  if (matches != 1)
    return 0;
  *diagnostic = (struct thumb_diagnostic){p, call, width, original,
                                          thumb_call_target(code, vm, call)};
  return 1;
}
static int thumb_literal_success(const unsigned char *code, uint64_t vm,
                                 const struct function *f,
                                 const unsigned char *boundary,
                                 const struct thumb_diagnostic *passed,
                                 const struct thumb_diagnostic *failed,
                                 size_t *target) {
  size_t after = passed->call + 4;
  int64_t cleanup;
  int condition;
  if (after >= f->end || !thumb_boundary(boundary, f, after) ||
      !thumb_branch(code, after, f->end, &cleanup, &condition) ||
      condition != -1 || cleanup <= (int64_t)failed->call + 6 ||
      cleanup >= (int64_t)f->end ||
      !thumb_boundary(boundary, f, (size_t)cleanup))
    return 0;
  size_t begin = passed->site - f->begin > 16 ? passed->site - 16 : f->begin;
  size_t count = 0;
  for (size_t p = begin; p < passed->site; p += 2) {
    if (!thumb_boundary(boundary, f, p) || (le16(code + p) & 0xf800) != 0x4800)
      continue;
    unsigned reg = (le16(code + p) >> 8) & 7;
    uint64_t pool = ((vm + p + 4) & ~UINT64_C(3)) + (le16(code + p) & 255) * 4;
    if (pool < vm + f->begin || pool > vm + f->end || vm + f->end - pool < 4)
      continue;
    size_t previous;
    int64_t destination;
    if (!thumb_previous(code, boundary, f, p, &previous) ||
        !thumb_boundary(boundary, f, previous) ||
        !thumb_branch(code, previous, f->end, &destination, &condition) ||
        condition != -1 || destination != (int64_t)failed->site)
      continue;
    size_t q = p + 2;
    int pic = le16(code + q) == (0x4478 | reg);
    if (pic != (passed->call - passed->site - passed->width == 2))
      continue;
    if (pic)
      q += 2;
    if (q >= passed->site || passed->site - q < 6 ||
        le16(code + q) != (0x6800 | (reg << 3) | reg) ||
        le16(code + q + 2) != (0x6800 | (reg << 3) | reg))
      continue;
    q += 4;
    int compare = le16(code + q) == (0x2800 | (reg << 8));
    if (compare)
      q += 2;
    if (q >= passed->site || !thumb_boundary(boundary, f, q) ||
        !thumb_branch(code, q, f->end, &destination, &condition) ||
        destination != cleanup || q + thumb_size(code, q) != passed->site ||
        (compare ? condition != 0
                 : (condition != 16 || (le16(code + q) & 7) != reg)))
      continue;
    *target = p;
    ++count;
  }
  return count == 1;
}
static int thumb_load(const unsigned char *code, size_t p, unsigned *rd,
                      unsigned *rn, unsigned *immediate) {
  unsigned first = le16(code + p);
  if ((first & 0xf800) == 0x9800) {
    *rd = (first >> 8) & 7;
    *rn = 13;
    *immediate = (first & 255) * 4;
  } else if ((first & 0xf800) == 0x6800) {
    *rd = first & 7;
    *rn = (first >> 3) & 7;
    *immediate = ((first >> 6) & 31) * 4;
  } else if ((first & 0xfff0) == 0xf8d0) {
    *rn = first & 15;
    *rd = le16(code + p + 2) >> 12;
    *immediate = le16(code + p + 2) & 4095;
  } else {
    return 0;
  }
  return *rd < 13 && (*rn == 13 || (*rn < 13 && !*immediate));
}
/* Preserve success-path reloads and flags. */
static int thumb_success(const unsigned char *code, const struct function *f,
                         const unsigned char *boundary,
                         const struct thumb_diagnostic *passed,
                         size_t *target) {
  size_t guard = 0, count = 0;
  unsigned reg = 0;
  size_t begin = passed->site - f->begin > 130 ? passed->site - 130 : f->begin;
  for (size_t p = begin; p < passed->site; p += 2) {
    if (!thumb_boundary(boundary, f, p) || (le16(code + p) & 0xf500) != 0xb100)
      continue;
    int64_t destination;
    int condition;
    if (!thumb_branch(code, p, f->end, &destination, &condition))
      continue;
    if (condition == 16 && p + 2 == passed->site &&
        destination == (int64_t)passed->call + 4) {
      guard = p;
    } else if (condition == 17 && destination == (int64_t)passed->site) {
      size_t q = p + 2;
      unsigned rd, rn, imm;
      while (q < passed->site && thumb_boundary(boundary, f, q) &&
             thumb_load(code, q, &rd, &rn, &imm) && rn == 13)
        q += thumb_size(code, q);
      if (q >= passed->site || !thumb_boundary(boundary, f, q) ||
          !thumb_branch(code, q, f->end, &destination, &condition) ||
          condition != -1 || q + thumb_size(code, q) != passed->site ||
          destination < (int64_t)f->begin || destination >= (int64_t)f->end ||
          !thumb_boundary(boundary, f, (size_t)destination) ||
          (destination >= (int64_t)passed->site &&
           destination <= (int64_t)passed->call))
        continue;
      guard = p;
    } else {
      continue;
    }
    reg = le16(code + p) & 7;
    ++count;
  }
  if (count != 1)
    return 0;
  size_t start = guard, previous = 0;
  unsigned instructions = 0;
  while (thumb_previous(code, boundary, f, start, &previous)) {
    unsigned rd, rn, imm, op = le16(code + previous);
    if (!thumb_boundary(boundary, f, previous) ||
        (!thumb_load(code, previous, &rd, &rn, &imm) &&
         (op & 0xf8ff) != 0x2001))
      break;
    if (++instructions > 6 || guard - previous > 24)
      return 0;
    start = previous;
  }
  unsigned rd, rn, imm;
  if (!instructions || !thumb_load(code, start, &rd, &rn, &imm) || rn != 13 ||
      !thumb_previous(code, boundary, f, start, &previous))
    return 0;
  int64_t branch;
  int condition;
  if (!thumb_call(code, previous, f->end) &&
      !thumb_branch(code, previous, f->end, &branch, &condition))
    return 0;
  unsigned pointers = 0;
  for (size_t p = start; p < guard; p += thumb_size(code, p)) {
    if (thumb_load(code, p, &rd, &rn, &imm)) {
      if (rn == 13) {
        pointers |= 1u << rd;
      } else {
        if (!(pointers & (1u << rn)))
          return 0;
        pointers &= ~(1u << rd);
      }
    } else {
      rd = (le16(code + p) >> 8) & 7;
      pointers &= ~(1u << rd);
    }
  }
  if (!thumb_previous(code, boundary, f, guard, &previous) ||
      !thumb_load(code, previous, &rd, &rn, &imm) || rn == 13 || rd != reg)
    return 0;
  *target = start;
  return 1;
}
static size_t legacy_body_end(const unsigned char *code,
                              const struct function *f) {
  if (f->end - f->begin < 20 || le32(code + f->begin) != 0xaf03b5f0u ||
      le32(code + f->begin + 4) != 0x0d00e92du ||
      (le16(code + f->begin + 8) & 0xff80) != 0xb080)
    return 0;
  for (size_t p = f->begin; f->end - p >= 10; p += thumb_size(code, p))
    if (le32(code + p) == 0x0d18f1a7u && le32(code + p + 4) == 0x0d00e8bdu &&
        le16(code + p + 8) == 0xbdf0)
      return p + 10;
  return 0;
}
static int armv7(unsigned char *b, const struct image *im) {
  uint64_t failed = 0, passed = 0;
  if (literal(b, &im->strings, "Image failed signature verification",
              &failed) ||
      literal(b, &im->strings, "Image passed signature verification", &passed))
    return -1;
  if (im->text.address % 2 || im->text.offset % 2 || im->text.length % 2)
    return error("unaligned Thumb text");
  const unsigned char *code = b + im->text.offset;
  struct thumb_diagnostic failure = {0}, success = {0};
  const struct function *ff = NULL, *sf = NULL;
  size_t nf = 0, np = 0;
  int (*diagnostic)(const unsigned char *, uint64_t, const struct function *,
                    const unsigned char *, size_t, uint64_t, int,
                    struct thumb_diagnostic *) =
      im->have_functions ? thumb_diagnostic : thumb_literal_diagnostic;
  for (size_t i = 0; i < im->nfunctions; ++i) {
    const struct function *f = &im->bounds[i];
    if (!f->thumb)
      continue;
    size_t end = im->have_functions ? f->end : legacy_body_end(code, f);
    if (!end)
      continue;
    unsigned char *boundary = calloc(f->end - f->begin, 1);
    if (!boundary)
      return error("out of memory");
    if (thumb_boundaries(code, f->begin, end, boundary)) {
      for (size_t p = f->begin; p < end; p += thumb_size(code, p)) {
        if (diagnostic(code, im->text.address, f, boundary, p, failed, 1,
                       &failure)) {
          ff = f;
          ++nf;
        }
        if (diagnostic(code, im->text.address, f, boundary, p, passed, 0,
                       &success)) {
          sf = f;
          ++np;
        }
      }
    }
    free(boundary);
  }
  if (nf != 1 || np != 1 || ff != sf || failure.logger != success.logger)
    return error("unrecognized or ambiguous Thumb signature diagnostics");
  unsigned char *boundary = calloc(sf->end - sf->begin, 1);
  if (!boundary)
    return error("out of memory");
  size_t target = 0;
  uint32_t replacement = 0;
  size_t end = im->have_functions ? sf->end : legacy_body_end(code, sf);
  int recognized =
      end && thumb_boundaries(code, sf->begin, end, boundary) &&
      (im->have_functions
           ? thumb_success(code, sf, boundary, &success, &target)
           : thumb_literal_success(code, im->text.address, sf, boundary,
                                   &success, &failure, &target));
  if (recognized && failure.width == 2) {
    int64_t delta = (int64_t)target - (int64_t)failure.site - 4;
    recognized = !(delta % 2) && delta >= -2048 && delta <= 2046;
    replacement = (failure.original & 0xffff0000u) | 0xe000u |
                  ((uint32_t)(delta / 2) & 0x7ff);
  } else if (recognized) {
    recognized = thumb_jump(failure.site, target, &replacement);
  }
  free(boundary);
  if (!recognized)
    return error("unrecognized Thumb success/cleanup path");
  uint32_t original = le32(code + failure.site);
  if (original != failure.original && original != replacement)
    return error("unrecognized existing Thumb patch");
  printf("ARMv7%s%s\n  file 0x%zx: %08" PRIx32 " -> %08" PRIx32
         " (target VM 0x%" PRIx64 ")\n",
         im->subtype == 11 ? "s" : "",
         original == replacement ? " (already patched)" : "",
         im->text.offset + failure.site, original, replacement,
         im->text.address + target);
  put32(b + im->text.offset + failure.site, replacement);
  return 0;
}

static void arm64_refs(const unsigned char *b, const struct section *s,
                       uint64_t failed, uint64_t passed, size_t *fail,
                       size_t *pass, size_t *nf, size_t *np) {
  uint64_t value[31] = {0};
  unsigned char valid[31] = {0};
  for (size_t off = 0; off + 4 <= s->length; off += 4) {
    uint32_t op = le32(b + s->offset + off);
    unsigned rd = op & 31, rn = (op >> 5) & 31;
    uint64_t target = 0;
    size_t site = off;
    int found = 0;
    if ((op & 0x7c000000u) == 0x14000000u ||
        (op & 0xff000010u) == 0x54000000u ||
        (op & 0x7e000000u) == 0x34000000u ||
        (op & 0x7e000000u) == 0x36000000u ||
        (op & 0xff000000u) == 0xd6000000u) {
      memset(valid, 0, sizeof(valid));
      continue;
    }
    if (rd == 31)
      continue;
    if ((op & 0x9f000000u) == 0x90000000u) {
      int64_t imm =
          sx(((op >> 29) & 3) | ((uint64_t)((op >> 5) & 0x7ffff) << 2), 21);
      value[rd] = ((s->address + off) & ~UINT64_C(4095)) + imm * 4096;
      valid[rd] = 1;
      continue;
    } else if ((op & 0x9f000000u) == 0x10000000u) {
      target =
          s->address + off +
          sx(((op >> 29) & 3) | ((uint64_t)((op >> 5) & 0x7ffff) << 2), 21);
      found = 1;
    } else if ((op & 0xff800000u) == 0x91000000u) {
      if (rn != 31 && valid[rn]) {
        target = value[rn] + ((uint64_t)((op >> 10) & 4095)
                              << ((op & (1u << 22)) ? 12 : 0));
        found = 1;
      }
    } else if ((op & 0xffc00000u) == 0xf9400000u) {
      if (rn != 31 && valid[rn] && ((op >> 10) & 4095)) {
        target = value[rn] + ((uint64_t)((op >> 10) & 4095) << 3);
        found = 1;
      }
    } else if ((op & 0xff000000u) == 0x58000000u) {
      target = s->address + off + sx((op >> 5) & 0x7ffff, 19) * 4;
      found = 1;
    }
    valid[rd] = found;
    value[rd] = target;
    if (!found)
      continue;
    /* Patch adjacent ADRP/ADD pairs at the ADRP. */
    if ((op & 0xffc00000u) == 0x91000000u && rd == rn && off >= 4) {
      uint32_t previous = le32(b + s->offset + off - 4);
      if ((previous & 0x9f00001fu) == (0x90000000u | rn))
        site -= 4;
    }
    if (target == failed) {
      *fail = site;
      ++*nf;
    }
    if (target == passed) {
      *pass = site;
      ++*np;
    }
    /* Track load addresses, not loaded values. */
    if ((op & 0xffc00000u) == 0xf9400000u || (op & 0xff000000u) == 0x58000000u)
      valid[rd] = 0;
  }
}
static int64_t arm64_target(size_t p, uint32_t op) {
  return (int64_t)p + sx(op & 0x3ffffff, 26) * 4;
}
static int arm64_log(const unsigned char *code, size_t p, size_t end,
                     int patched, uint64_t string, int64_t *logger) {
  if (p > end || end - p < 12)
    return 0;
  uint32_t first = le32(code + p), second = le32(code + p + 4),
           call = le32(code + p + 8);
  int adr = (first & 0x9f00001fu) == 0x10000000u,
      adrp = (first & 0x9f00001fu) == 0x90000000u;
  if (patched) {
    if ((first & 0xfc000000u) != 0x14000000u)
      return 0;
    adr = second == 0xd503201fu;
    adrp = (second & 0xffc003ffu) == 0x91000000u &&
           ((second >> 10) & 4095) == (string & 4095);
  }
  if ((!adr || second != 0xd503201fu) &&
      (!adrp || (second & 0xffc003ffu) != 0x91000000u))
    return 0;
  if ((call & 0xfc000000u) != 0x94000000u)
    return 0;
  *logger = arm64_target(p + 8, call);
  return 1;
}
static int arm64_error_status(const unsigned char *code, size_t p, size_t end) {
  if (p > end || end - p < 4)
    return 0;
  /* Some builds set the stream-open flag first. */
  uint32_t first = le32(code + p);
  if ((first & 0xffffffe0u) == 0x52800020u) {
    p += 4;
    if (end - p < 4 || (first & 31) == (le32(code + p) & 31))
      return 0;
  }
  return (le32(code + p) & 0xffffffe0u) == 0x52800a00u;
}
static int arm64(unsigned char *b, const struct image *im) {
  uint64_t failed = 0, passed = 0;
  if (literal(b, &im->strings, "Image failed signature verification",
              &failed) ||
      literal(b, &im->strings, "Image passed signature verification", &passed))
    return -1;
  const struct section *s = &im->text;
  const unsigned char *code = b + s->offset;
  size_t fail = 0, pass = 0, nf = 0, np = 0, site = 0, count = 0;
  arm64_refs(b, s, failed, passed, &fail, &pass, &nf, &np);
  if (np != 1 || nf > 1)
    return error("unrecognized or ambiguous ARM64 signature references");
  const struct function *success = function_at(im, pass);
  int64_t logger = 0, failure_logger = 0;
  if (!success || !arm64_log(code, pass, success->end, 0, passed, &logger))
    return error("unrecognized ARM64 success diagnostic");
  int already = 0, helper = 0;
  if (nf == 1) {
    const struct function *failure = function_at(im, fail);
    if (!failure ||
        !arm64_log(code, fail, failure->end, 0, failed, &failure_logger) ||
        failure_logger != logger)
      return error("unrecognized ARM64 failure diagnostic");
    if (failure == success) {
      if (!arm64_error_status(code, fail + 12, failure->end))
        return error("unrecognized ARM64 signature error status");
      site = fail;
      count = 1;
    } else {
      /* Patch the caller; the helper has its own stack frame. */
      helper = 1;
      if (fail - failure->begin > 32)
        return error("unrecognized ARM64 failure helper");
      for (size_t p = 0; p + 4 <= s->length; p += 4) {
        uint32_t op = le32(code + p);
        int original = (op & 0xfc000000u) == 0x94000000u &&
                       arm64_target(p, op) == (int64_t)failure->begin;
        int patched = (op & 0xfc000000u) == 0x14000000u &&
                      arm64_target(p, op) == (int64_t)pass &&
                      arm64_error_status(code, p + 4, success->end);
        if (!original && !patched)
          continue;
        if (function_at(im, p) != success ||
            !arm64_error_status(code, p + 4, success->end))
          return error("unrecognized ARM64 failure-helper caller");
        site = p;
        already = patched;
        ++count;
      }
    }
  } else {
    for (size_t p = 0; p + 4 <= s->length; p += 4) {
      uint32_t op = le32(code + p);
      if ((op & 0xfc000000u) != 0x14000000u ||
          arm64_target(p, op) != (int64_t)pass)
        continue;
      if (function_at(im, p) != success)
        return error("unsafe existing ARM64 patch crosses function boundaries; "
                     "use original ASR");
      if (!arm64_log(code, p, success->end, 1, failed, &failure_logger) ||
          failure_logger != logger ||
          !arm64_error_status(code, p + 12, success->end))
        continue;
      site = p;
      already = 1;
      ++count;
    }
  }
  if (count != 1 || site == pass)
    return error("unrecognized or ambiguous ARM64 signature verification");
  int64_t delta = (int64_t)pass - (int64_t)site;
  if (delta % 4 || delta < -(INT64_C(1) << 27) || delta >= (INT64_C(1) << 27))
    return error("ARM64 branch out of range");
  uint32_t branch = 0x14000000u | ((uint32_t)(delta / 4) & 0x3ffffff);
  printf("ARM64 %s%s\n  file 0x%zx: %08" PRIx32 " -> %08" PRIx32
         " (target VM 0x%" PRIx64 ")\n",
         helper ? "failure helper" : "inline",
         already ? " (already patched)" : "", s->offset + site,
         le32(code + site), branch, s->address + pass);
  put32(b + s->offset + site, branch);
  return 0;
}
static int write_atomic(const char *path, const unsigned char *b, size_t n,
                        mode_t mode) {
  size_t len = strlen(path);
  if (len > SIZE_MAX - 12)
    return error("output path too long");
  char *temp = malloc(len + 12);
  if (!temp)
    return error("out of memory");
  snprintf(temp, len + 12, "%s.tmp.XXXXXX", path);
  int fd = mkstemp(temp), result = -1;
  if (fd < 0) {
    perror("create output temporary file");
    free(temp);
    return -1;
  }
  FILE *fp = fdopen(fd, "wb");
  if (!fp) {
    perror("open output stream");
    close(fd);
    goto done;
  }
  int bad = fwrite(b, 1, n, fp) != n;
  if (!bad && fflush(fp))
    bad = 1;
  if (!bad && fchmod(fd, mode & 0777))
    bad = 1;
  if (!bad && fsync(fd))
    bad = 1;
  if (fclose(fp))
    bad = 1;
  if (bad) {
    perror("write output");
    goto done;
  }
  if (rename(temp, path)) {
    perror("rename output");
    goto done;
  }
  result = 0;
done:
  if (result)
    unlink(temp);
  free(temp);
  return result;
}
int main(int argc, char **argv) {
  int dry = argc > 1 && !strcmp(argv[1], "--dry-run");
  if ((!dry && argc != 3) || (dry && argc != 3 && argc != 4)) {
    fprintf(
        stderr,
        "Usage: %s ASR Patched_ASR\n       %s --dry-run ASR [Patched_ASR]\n",
        argv[0], argv[0]);
    return 1;
  }
  const char *input = argv[1 + dry];
  int input_fd = open(input, O_RDONLY | O_NONBLOCK);
  if (input_fd < 0) {
    perror(input);
    return 1;
  }
  FILE *fp = fdopen(input_fd, "rb");
  if (!fp) {
    perror(input);
    close(input_fd);
    return 1;
  }
  struct stat st;
  if (fstat(fileno(fp), &st) || !S_ISREG(st.st_mode) || st.st_size <= 0 ||
      st.st_size > 128 * 1024 * 1024) {
    error("input must be a nonempty regular file of at most 128 MiB");
    fclose(fp);
    return 1;
  }
  size_t n = (size_t)st.st_size;
  unsigned char *b = malloc(n);
  if (!b) {
    error("out of memory");
    fclose(fp);
    return 1;
  }
  int bad = fread(b, 1, n, fp) != n;
  if (!bad && fgetc(fp) != EOF)
    bad = 1;
  if (ferror(fp))
    bad = 1;
  if (fclose(fp))
    bad = 1;
  if (bad) {
    error("could not read complete input");
    free(b);
    return 1;
  }
  struct image im = {0};
  int result = parse(b, n, &im);
  if (!result)
    result = function_starts(b, &im);
  if (!result)
    result = im.cpu != 12       ? arm64(b, &im)
             : im.subtype == 12 ? watch(b, &im)
                                : armv7(b, &im);
  if (!result && !dry)
    result = write_atomic(argv[2], b, n, st.st_mode);
  if (!result)
    puts(dry ? "Dry run: no output written." : "Patched ASR written.");
  free(im.bounds);
  free(b);
  return result ? 1 : 0;
}
