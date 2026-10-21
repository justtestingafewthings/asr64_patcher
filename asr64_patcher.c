#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <string.h>
#include <fcntl.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <unistd.h>

struct section {
  uint64_t address;
  size_t offset, length;
};
struct image {
  uint32_t cpu, subtype;
  struct section text, strings;
  uint64_t base;
  size_t functions, functions_length;
};
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

/* Thin little-endian Mach-O only. */
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
      (!wide && (im->cpu != 12 || im->subtype != 12)))
    return error("unsupported architecture, expected ARM64 or ARMv7k");
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
      if (size != 16 || im->functions_length ||
          !range(le32(b + p + 8), le32(b + p + 12), n))
        return error("invalid function starts");
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
static uint16_t le16(const unsigned char *p) {
  return (uint16_t)p[0] | (uint16_t)p[1] << 8;
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
      int64_t delta = (int64_t)success - (int64_t)site - 4;
      if (delta % 2 || delta < -(INT64_C(1) << 24) ||
          delta >= (INT64_C(1) << 24))
        continue;
      uint32_t d = (uint32_t)delta, s = (d >> 24) & 1;
      replacement = 0xf000u | (s << 10) | ((d >> 12) & 0x3ff) |
                    ((0x9000u | ((1 ^ ((d >> 23) & 1) ^ s) << 13) |
                      ((1 ^ ((d >> 22) & 1) ^ s) << 11) | ((d >> 1) & 0x7ff))
                     << 16);
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
static int watch_function(const unsigned char *code, const struct section *text,
                          size_t begin, size_t end, uint64_t failed,
                          uint64_t passed, size_t *failure_function,
                          struct thumb_patch *patch) {
  unsigned char *boundary = calloc(end - begin, 1);
  if (!boundary)
    return error("out of memory");
  size_t fail = 0, pass = 0, nf = 0, np = 0;
  unsigned it = 0;
  for (size_t p = begin; p < end;) {
    size_t length = thumb_size(code, p);
    if (end - p < length) {
      free(boundary);
      return 0;
    }
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
    if (thumb_string(code, p, end, text->address, failed)) {
      fail = p;
      ++nf;
    }
    if (passed && thumb_string(code, p, end, text->address, passed)) {
      pass = p;
      ++np;
    }
    p += length;
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
    uint64_t address = im->base, delta = 0;
    size_t begin = 0;
    unsigned shift = 0;
    int have_begin = 0, terminated = 0;
    count = 0;
    for (size_t i = 0; i < im->functions_length; ++i) {
      unsigned byte = b[im->functions + i];
      if (shift >= 63 || (uint64_t)(byte & 127) > (UINT64_MAX >> shift))
        return error("invalid function-start delta");
      delta |= (uint64_t)(byte & 127) << shift;
      if (byte & 128) {
        shift += 7;
        continue;
      }
      if (!delta) {
        terminated = 1;
        break;
      }
      if (address > UINT64_MAX - delta)
        return error("function-start overflow");
      address += delta;
      uint64_t pc = address & ~UINT64_C(1);
      if (pc < im->text.address || pc - im->text.address >= im->text.length ||
          (have_begin && pc - im->text.address <= begin))
        return error("invalid function boundary");
      size_t end = (size_t)(pc - im->text.address);
      if (have_begin) {
        int found =
            watch_function(code, &im->text, begin, end, failed,
                           round ? passed : 0, &failure_function, &patch);
        if (found < 0)
          return -1;
        count += found;
      }
      begin = end;
      have_begin = (address & 1) != 0;
      shift = 0;
      delta = 0;
    }
    if (!terminated)
      return error("unterminated function starts");
    if (have_begin) {
      int found =
          watch_function(code, &im->text, begin, im->text.length, failed,
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

/* Legacy xref64 address tracking in VM space. */
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
static int arm64(unsigned char *b, const struct image *im) {
  uint64_t failed = 0, passed = 0;
  if (literal(b, &im->strings, "Image failed signature verification",
              &failed) ||
      literal(b, &im->strings, "Image passed signature verification", &passed))
    return -1;
  const struct section *s = &im->text;
  size_t fail = 0, pass = 0, nf = 0, np = 0;
  arm64_refs(b, s, failed, passed, &fail, &pass, &nf, &np);
  if (np != 1 || nf > 1)
    return error("unrecognized or ambiguous ARM64 signature references");
  int already = 0;
  if (nf == 0) {
    for (size_t off = 0; off + 4 <= s->length; off += 4) {
      uint32_t a = le32(b + s->offset + off);
      if ((a & 0xfc000000u) != 0x14000000u)
        continue;
      uint64_t target = s->address + off + sx(a & 0x3ffffff, 26) * 4;
      if (target != s->address + pass)
        continue;
      fail = off;
      ++nf;
    }
    already = 1;
  }
  if (nf != 1 || fail == pass)
    return error("unrecognized ARM64 signature references");
  int64_t delta = (int64_t)pass - (int64_t)fail;
  if (delta % 4 || delta < -(INT64_C(1) << 27) || delta >= (INT64_C(1) << 27))
    return error("ARM64 branch out of range");
  uint32_t branch = 0x14000000u | ((uint32_t)(delta / 4) & 0x3ffffff);
  printf("ARM64 legacy pattern%s\n  file 0x%zx: %08" PRIx32 " -> %08" PRIx32
         " (target VM 0x%" PRIx64 ")\n",
         already ? " (already patched)" : "", s->offset + fail,
         le32(b + s->offset + fail), branch, s->address + pass);
  put32(b + s->offset + fail, branch);
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
    result = im.cpu == 12 ? watch(b, &im) : arm64(b, &im);
  if (!result && !dry)
    result = write_atomic(argv[2], b, n, st.st_mode);
  if (!result)
    puts(dry ? "Dry run: no output written." : "Patched ASR written.");
  free(b);
  return result ? 1 : 0;
}
