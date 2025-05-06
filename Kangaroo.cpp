#include <string.h>

#include <fstream>

#include "Kangaroo.h"
#include "SECPK1/IntGroup.h"
#include "Timer.h"
#define _USE_MATH_DEFINES
#include <math.h>

#include <algorithm>
#include <memory>
#ifndef WIN64
#include <pthread.h>
#endif

#include <openssl/evp.h>
#include <string>
#include <iomanip>
#include <vector>

using namespace std;

#define safe_delete_array(x) \
  if (x) {                   \
    delete[] x;              \
    x = NULL;                \
  }

// Function to convert a Point to a Bitcoin address
std::string PointToAddress(const Point& point) {
    unsigned char pubKey[33];
    pubKey[0] = point.y.IsOdd() ? 0x03 : 0x02; // 0x02 for even y, 0x03 for odd
    unsigned char xBytes[32];
    point.x.Get32Bytes(xBytes);
    memcpy(pubKey + 1, xBytes, 32);

    // SHA-256 with EVP
    unsigned char hash1[32];
    EVP_MD_CTX* sha256_ctx = EVP_MD_CTX_new();
    EVP_DigestInit_ex(sha256_ctx, EVP_sha256(), NULL);
    EVP_DigestUpdate(sha256_ctx, pubKey, 33);
    EVP_DigestFinal_ex(sha256_ctx, hash1, NULL);
    EVP_MD_CTX_free(sha256_ctx);

    // RIPEMD-160 with EVP
    unsigned char hash2[20];
    EVP_MD_CTX* ripemd160_ctx = EVP_MD_CTX_new();
    EVP_DigestInit_ex(ripemd160_ctx, EVP_ripemd160(), NULL);
    EVP_DigestUpdate(ripemd160_ctx, hash1, 32);
    EVP_DigestFinal_ex(ripemd160_ctx, hash2, NULL);
    EVP_MD_CTX_free(ripemd160_ctx);

    // Add version (0x00 for mainnet)
    unsigned char extended[21];
    extended[0] = 0x00;
    memcpy(extended + 1, hash2, 20);

    // Double SHA-256 for checksum with EVP
    unsigned char hash3[32];
    EVP_MD_CTX* sha256_ctx2 = EVP_MD_CTX_new();
    EVP_DigestInit_ex(sha256_ctx2, EVP_sha256(), NULL);
    EVP_DigestUpdate(sha256_ctx2, extended, 21);
    EVP_DigestFinal_ex(sha256_ctx2, hash3, NULL);
    EVP_MD_CTX_free(sha256_ctx2);

    unsigned char hash4[32];
    EVP_MD_CTX* sha256_ctx3 = EVP_MD_CTX_new();
    EVP_DigestInit_ex(sha256_ctx3, EVP_sha256(), NULL);
    EVP_DigestUpdate(sha256_ctx3, hash3, 32);
    EVP_DigestFinal_ex(sha256_ctx3, hash4, NULL);
    EVP_MD_CTX_free(sha256_ctx3);

    // Checksum (first 4 bytes)
    unsigned char checksum[4];
    memcpy(checksum, hash4, 4);

    // Final address (21 + 4 = 25 bytes)
    unsigned char final[25];
    memcpy(final, extended, 21);
    memcpy(final + 21, checksum, 4);

    // Base58 encoding
    const char* b58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    std::string result;
    unsigned long long carry;
    std::vector<unsigned char> temp(final, final + 25);
    for (int i = 24; i >= 0; i--) {
        carry = temp[i];
        for (size_t j = 0; j < result.length(); j++) {
            carry += (unsigned long long)(unsigned char)result[j] << 8;
            result[j] = b58[carry % 58];
            carry /= 58;
        }
        while (carry) {
            result += b58[carry % 58];
            carry /= 58;
        }
    }
    std::reverse(result.begin(), result.end());
    while (result.length() > 0 && result[0] == b58[0]) result.erase(0, 1); // Remove leading ones
    return result;
}

// ----------------------------------------------------------------------------

Kangaroo::Kangaroo(Secp256K1 *secp, int32_t initDPSize, bool useGpu,
                   string &workFile, string &iWorkFile, uint32_t savePeriod,
                   bool saveKangaroo, bool saveKangarooByServer, double maxStep,
                   int wtimeout, int port, int ntimeout, string serverIp,
                   string outputFile, bool splitWorkfile) {
  this->secp = secp;
  this->initDPSize = initDPSize;
  this->useGpu = useGpu;
  this->offsetCount = 0;
  this->offsetTime = 0.0;
  this->workFile = workFile;
  this->saveWorkPeriod = savePeriod;
  this->inputFile = iWorkFile;
  this->nbLoadedWalk = 0;
  this->clientMode = serverIp.length() > 0;
  this->saveKangarooByServer = this->clientMode && saveKangarooByServer;
  this->saveKangaroo = saveKangaroo || this->saveKangarooByServer;
  this->fRead = NULL;
  this->maxStep = maxStep;
  this->wtimeout = wtimeout;
  this->port = port;
  this->ntimeout = ntimeout;
  this->serverIp = serverIp;
  this->outputFile = outputFile;
  this->hostInfo = NULL;
  this->endOfSearch = false;
  this->saveRequest = false;
  this->connectedClient = 0;
  this->totalRW = 0;
  this->collisionInSameHerd = 0;
  this->keyIdx = 0;
  this->splitWorkfile = splitWorkfile;
  this->pid = Timer::getPID();

  CPU_GRP_SIZE = 1024;

  // Init mutex
#ifdef WIN64
  ghMutex = CreateMutex(NULL, FALSE, NULL);
  saveMutex = CreateMutex(NULL, FALSE, NULL);
#else
  pthread_mutex_init(&ghMutex, NULL);
  pthread_mutex_init(&saveMutex, NULL);
  signal(SIGPIPE, SIG_IGN);
#endif
}

// ----------------------------------------------------------------------------

bool Kangaroo::ParseConfigFile(std::string &fileName) {
  // In client mode, config come from the server
  if (clientMode) return true;

  // Check file
  FILE *fp = fopen(fileName.c_str(), "rb");
  if (fp == NULL) {
    ::printf("[+] Error: Cannot open %s %s\n", fileName.c_str(), strerror(errno));
    return false;
  }
  fclose(fp);

  // Get lines
  vector<string> lines;
  int nbLine = 0;
  string line;
  ifstream inFile(fileName);
  while (getline(inFile, line)) {
    // Remove ending \r\n
    int l = (int)line.length() - 1;
    while (l >= 0 && isspace(line.at(l))) {
      line.pop_back();
      l--;
    }
    if (line.length() > 0) {
      lines.push_back(line);
      nbLine++;
    }
  }

  if (lines.size() < 2) {
    ::printf("[+] Error: %s not enough arguments (need range start and end)\n", fileName.c_str());
    return false;
  }

  rangeStart.SetBase16((char *)lines[0].c_str());
  rangeEnd.SetBase16((char *)lines[1].c_str());
  // Игнорируем оставшиеся строки (публичные ключи)
  if (lines.size() > 2) {
    ::printf("[+] Warning: Ignoring public keys in %s (using hardcoded address)\n", fileName.c_str());
  }

  ::printf("[+] Start:%s\n", rangeStart.GetBase16().c_str());
  ::printf("[+] Stop :%s\n", rangeEnd.GetBase16().c_str());
  ::printf("[+] Keys : 0 (using hardcoded address)\n");

  return true;
}

// ----------------------------------------------------------------------------

bool Kangaroo::IsDP(Int *x) {
  return ((x->bits64[3] & dMask.i64[3]) == 0) &&
         ((x->bits64[2] & dMask.i64[2]) == 0) &&
         ((x->bits64[1] & dMask.i64[1]) == 0) &&
         ((x->bits64[0] & dMask.i64[0]) == 0);
}

void Kangaroo::SetDP(int size) {
  // Mask for distinguised point
  dpSize = size;
  dMask.i64[0] = 0;
  dMask.i64[1] = 0;
  dMask.i64[2] = 0;
  dMask.i64[3] = 0;
  if (dpSize > 0) {
    if (dpSize > 256) dpSize = 256;
    for (int i = 0; i < size; i += 64) {
      int end = (i + 64 > size) ? (size - 1) % 64 : 63;
      uint64_t mask = ((1ULL << end) - 1) << 1 | 1ULL;
      dMask.i64[(int)(i / 64)] = mask;
    }
  }

#ifdef WIN64
  ::printf("[+] DP size: %d [0x%016I64X %016I64X %016I64X %016I64X]\n", dpSize,
      dMask.i64[3], dMask.i64[2], dMask.i64[1], dMask.i64[0]);
#else
  ::printf("[+] DP size: %d [0x%" PRIx64 "%" PRIx64 "%" PRIx64 "%" PRIx64 "]\n",
           dpSize, dMask.i64[3], dMask.i64[2], dMask.i64[1], dMask.i64[0]);
#endif
}

// ----------------------------------------------------------------------------

bool Kangaroo::Output(Int *pk, char sInfo, int sType) {
  FILE *f = stdout;
  bool needToClose = false;

  if (outputFile.length() > 0) {
    f = fopen(outputFile.c_str(), "a");
    if (f == NULL) {
      printf("[+] Cannot open %s for writing\n", outputFile.c_str());
      f = stdout;
    } else {
      needToClose = true;
    }
  }

  if (!needToClose) ::printf("\n");

  Point PR = secp->ComputePublicKey(pk);

  ::fprintf(f, "Key#%2d [%d%c]Pub: 0x%s \n", keyIdx, sType, sInfo,
            secp->GetPublicKeyHex(true, PR).c_str());
  ::fprintf(f, "Address: %s\n", PointToAddress(PR).c_str());
  ::fprintf(f, "Priv: 0x%s \n", pk->GetBase16().c_str());

  if (needToClose) fclose(f);

  return true;
}

// ----------------------------------------------------------------------------

bool Kangaroo::CheckKey(Int d1, Int d2, uint8_t type) {
  // Resolve equivalence collision

  if (type & 0x1) d1.ModNegK1order();
  if (type & 0x2) d2.ModNegK1order();

  Int pk(&d1);
  pk.ModAddK1order(&d2);

  Point P = secp->ComputePublicKey(&pk);
  std::string computedAddress = PointToAddress(P);

  if (computedAddress == "1PWo3JeB9jrGwfHDNpdGK54CRas7fsVzXU") {
    // Key solved
#ifdef USE_SYMMETRY
    pk.ModAddK1order(&rangeWidthDiv2);
#endif
    pk.ModAddK1order(&rangeStart);
    return Output(&pk, 'N', type);
  }

  return false;
}

bool Kangaroo::CollisionCheck(Int *d1, uint32_t type1, Int *d2,
                              uint32_t type2) {
  if (type1 == type2) {
    // Collision inside the same herd
    return false;

  } else {
    Int Td;
    Int Wd;

    if (type1 == TAME) {
      Td.Set(d1);
      Wd.Set(d2);
    } else {
      Td.Set(d2);
      Wd.Set(d1);
    }

    endOfSearch = CheckKey(Td, Wd, 0) || CheckKey(Td, Wd, 1) ||
                  CheckKey(Td, Wd, 2) || CheckKey(Td, Wd, 3);
    if (!endOfSearch) {
      return false;
    }
  }

  return true;
}

// ----------------------------------------------------------------------------

bool Kangaroo::AddToTable(Int *pos, Int *dist, uint32_t kType) {
  int addStatus = hashTable.Add(pos, dist, kType);
  if (addStatus == ADD_COLLISION)
    return CollisionCheck(&hashTable.kDist, hashTable.kType, dist, kType);

  return addStatus == ADD_OK;
}

bool Kangaroo::AddToTable(int256_t *x, int256_t *d, uint32_t kType) {
  int addStatus = hashTable.Add(x, d, kType);
  if (addStatus == ADD_COLLISION) {
    Int dist;
    HashTable::toInt(d, &dist);
    return CollisionCheck(&hashTable.kDist, hashTable.kType, &dist, kType);
  }

  return addStatus == ADD_OK;
}

// ----------------------------------------------------------------------------

void Kangaroo::SolveKeyCPU(TH_PARAM *ph) {
  vector<ITEM> dps;
  double lastSent = 0;

  // Global init
  int thId = ph->threadId;

  // Create Kangaroos
  ph->nbKangaroo = CPU_GRP_SIZE;

#ifdef USE_SYMMETRY
  ph->symClass = new uint64_t[CPU_GRP_SIZE];
  for (int i = 0; i < CPU_GRP_SIZE; i++) ph->symClass[i] = 0;
#endif

  IntGroup *grp = new IntGroup(CPU_GRP_SIZE);
  Int *dx = new Int[CPU_GRP_SIZE];

  if (ph->px == NULL) {
    // Create Kangaroos, if not already loaded
    ph->px = new Int[CPU_GRP_SIZE];
    ph->py = new Int[CPU_GRP_SIZE];
    ph->distance = new Int[CPU_GRP_SIZE];
    CreateHerd(CPU_GRP_SIZE, ph->px, ph->py, ph->distance, TAME);
  }

  if (keyIdx == 0)
    ::printf("[+] SolveKeyCPU Thread %02d: %d kangaroos\n", ph->threadId,
             CPU_GRP_SIZE);

  ph->hasStarted = true;

  // Using Affine coord
  Int dy;
  Int rx;
  Int ry;
  Int _s;
  Int _p;

  while (!endOfSearch) {
    // Random walk

    for (int g = 0; g < CPU_GRP_SIZE; g++) {
#ifdef USE_SYMMETRY
      uint64_t jmp =
          ph->px[g].bits64[0] % (NB_JUMP / 2) + (NB_JUMP / 2) * ph->symClass[g];
#else
      uint64_t jmp = ph->px[g].bits64[0] % NB_JUMP;
#endif

      Int *p1x = &jumpPointx[jmp];
      Int *p2x = &ph->px[g];
      dx[g].ModSub(p2x, p1x);
    }

    grp->Set(dx);
    grp->ModInv();

    for (int g = 0; g < CPU_GRP_SIZE; g++) {
#ifdef USE_SYMMETRY
      uint64_t jmp =
          ph->px[g].bits64[0] % (NB_JUMP / 2) + (NB_JUMP / 2) * ph->symClass[g];
#else
      uint64_t jmp = ph->px[g].bits64[0] % NB_JUMP;
#endif

      Int *p1x = &jumpPointx[jmp];
      Int *p1y = &jumpPointy[jmp];
      Int *p2x = &ph->px[g];
      Int *p2y = &ph->py[g];

      dy.ModSub(p2y, p1y);
      _s.ModMulK1(&dy, &dx[g]);
      _p.ModSquareK1(&_s);

      rx.ModSub(&_p, p1x);
      rx.ModSub(p2x);

      ry.ModSub(p2x, &rx);
      ry.ModMulK1(&_s);
      ry.ModSub(p2y);

      ph->distance[g].ModAddK1order(&jumpDistance[jmp]);

#ifdef USE_SYMMETRY
      // Equivalence symmetry class switch
      if (ry.ModPositiveK1()) {
        ph->distance[g].ModNegK1order();
        ph->symClass[g] = !ph->symClass[g];
      }
#endif

      ph->px[g].Set(&rx);
      ph->py[g].Set(&ry);
    }

    if (clientMode) {
      // Send DP to server
      for (int g = 0; g < CPU_GRP_SIZE; g++) {
        if (IsDP(&ph->px[g])) {
          ITEM it;
          it.x.Set(&ph->px[g]);
          it.d.Set(&ph->distance[g]);
          it.kIdx = g;
          dps.push_back(it);
        }
      }

      double now = Timer::get_tick();
      if (now - lastSent > SEND_PERIOD) {
        LOCK(ghMutex);
        SendToServer(dps, ph->threadId, 0xFFFF);
        UNLOCK(ghMutex);
        lastSent = now;
      }

      if (!endOfSearch) counters[thId] += CPU_GRP_SIZE;

    } else {
      // Add to table and collision check
      for (int g = 0; g < CPU_GRP_SIZE && !endOfSearch; g++) {
        if (IsDP(&ph->px[g])) {
          LOCK(ghMutex);
          if (!endOfSearch) {
            // Create a Point object from px and py
            Point currentPoint;
            currentPoint.x.Set(&ph->px[g]);
            currentPoint.y.Set(&ph->py[g]);
            currentPoint.z.SetInt32(1); // Assuming affine coordinates

            // Compute the address from the point
            std::string address = PointToAddress(currentPoint);
            if (address == "1PWo3JeB9jrGwfHDNpdGK54CRas7fsVzXU") {
              // Address matches, save the private key
              Int privKey(&ph->distance[g]);
              // Adjust the private key with the range start
              privKey.ModAddK1order(&rangeStart);

              // Save to output file
              FILE* fp = fopen("E:\\135_kangaroo\\result71_1.txt", "a");
              if (fp) {
                fprintf(fp, "Address: %s\nPriv: 0x%s\n", address.c_str(), privKey.GetBase16().c_str());
                fclose(fp);
              }
              printf("Found address! Private key: 0x%s\n", privKey.GetBase16().c_str());
              endOfSearch = true; // Stop the search
            }

            if (!endOfSearch) {
              if (!AddToTable(&ph->px[g], &ph->distance[g], g % 2)) {
                // Collision inside the same herd
                // We need to reset the kangaroo
                CreateHerd(1, &ph->px[g], &ph->py[g], &ph->distance[g], g % 2, false);
                collisionInSameHerd++;
              }
            }
          }
          UNLOCK(ghMutex);
        }

        if (!endOfSearch) counters[thId]++;
      }
    }

    // Save request
    if (saveRequest && !endOfSearch) {
      ph->isWaiting = true;
      LOCK(saveMutex);
      ph->isWaiting = false;
      UNLOCK(saveMutex);
    }
  }

  // Free
  delete grp;
  delete[] dx;
  safe_delete_array(ph->px);
  safe_delete_array(ph->py);
  safe_delete_array(ph->distance);
#ifdef USE_SYMMETRY
  safe_delete_array(ph->symClass);
#endif

  ph->isRunning = false;
}

// ----------------------------------------------------------------------------

void Kangaroo::SolveKeyGPU(TH_PARAM *ph) {
  double lastSent = 0;

  // Global init
  int thId = ph->threadId;

#ifdef WITHGPU

  vector<ITEM> dps;
  vector<ITEM> gpuFound;
  GPUEngine *gpu;

  gpu = new GPUEngine(ph->gridSizeX, ph->gridSizeY, ph->gpuId, 65536 * 2);

  if (keyIdx == 0)
    ::printf("[+] GPU: %s (%.1f MB used)\n", gpu->deviceName.c_str(),
             gpu->GetMemory() / 1048576.0);

  double t0 = Timer::get_tick();

  if (ph->px == NULL) {
    if (keyIdx == 0)
      ::printf("[+] SolveKeyGPU Thread GPU#%d: creating kangaroos...\n",
               ph->gpuId);
    // Create Kangaroos, if not already loaded
    uint64_t nbThread = gpu->GetNbThread();
    ph->px = new Int[ph->nbKangaroo];
    ph->py = new Int[ph->nbKangaroo];
    ph->distance = new Int[ph->nbKangaroo];

    for (uint64_t i = 0; i < nbThread; i++) {
      CreateHerd(GPU_GRP_SIZE, &(ph->px[i * GPU_GRP_SIZE]),
                 &(ph->py[i * GPU_GRP_SIZE]), &(ph->distance[i * GPU_GRP_SIZE]),
                 TAME);
    }
  }

#ifdef USE_SYMMETRY
  gpu->SetWildOffset(&rangeWidthDiv4);
#else
  gpu->SetWildOffset(&rangeWidthDiv2);
#endif
  Int dmaskInt;
  HashTable::toInt(&dMask, &dmaskInt);
  gpu->SetParams(&dmaskInt, jumpDistance, jumpPointx, jumpPointy);
  gpu->SetKangaroos(ph->px, ph->py, ph->distance);

  if (workFile.length() == 0 || !saveKangaroo) {
    // No need to get back kangaroo, free memory
    safe_delete_array(ph->px);
    safe_delete_array(ph->py);
    safe_delete_array(ph->distance);
  }

  gpu->callKernel();

  double t1 = Timer::get_tick();

  if (keyIdx == 0)
    ::printf("[+] SolveKeyGPU Thread GPU#%d: 2^%.2f kangaroos [%.1fs]\n",
             ph->gpuId, log2((double)ph->nbKangaroo), (t1 - t0));

  ph->hasStarted = true;

  while (!endOfSearch) {
    gpu->Launch(gpuFound);
    counters[thId] += ph->nbKangaroo * NB_RUN;

    if (clientMode) {
      for (int i = 0; i < (int)gpuFound.size(); i++) dps.push_back(gpuFound[i]);

      double now = Timer::get_tick();
      if (now - lastSent > SEND_PERIOD) {
        LOCK(ghMutex);
        SendToServer(dps, ph->threadId, ph->gpuId);
        UNLOCK(ghMutex);
        lastSent = now;
      }

    } else {
      if (gpuFound.size() > 0) {
        LOCK(ghMutex);

        for (int g = 0; !endOfSearch && g < gpuFound.size(); g++) {
          uint32_t kType = (uint32_t)(gpuFound[g].kIdx % 2);

          if (!AddToTable(&gpuFound[g].x, &gpuFound[g].d, kType)) {
            // Collision inside the same herd
            // We need to reset the kangaroo
            Int px;
            Int py;
            Int d;
            CreateHerd(1, &px, &py, &d, kType, false);
            gpu->SetKangaroo(gpuFound[g].kIdx, &px, &py, &d);
            collisionInSameHerd++;
          }
        }
        UNLOCK(ghMutex);
      }
    }

    // Save request
    if (saveRequest && !endOfSearch) {
      // Get kangaroos
      if (saveKangaroo) gpu->GetKangaroos(ph->px, ph->py, ph->distance);
      ph->isWaiting = true;
      LOCK(saveMutex);
      ph->isWaiting = false;
      UNLOCK(saveMutex);
    }
  }

  safe_delete_array(ph->px);
  safe_delete_array(ph->py);
  safe_delete_array(ph->distance);
  delete gpu;

#else

  ph->hasStarted = true;

#endif

  ph->isRunning = false;
}

// ----------------------------------------------------------------------------

#ifdef WIN64
DWORD WINAPI _SolveKeyCPU(LPVOID lpParam) {
#else
void *_SolveKeyCPU(void *lpParam) {
#endif
  TH_PARAM *p = (TH_PARAM *)lpParam;
  p->obj->SolveKeyCPU(p);
  return 0;
}

#ifdef WIN64
DWORD WINAPI _SolveKeyGPU(LPVOID lpParam) {
#else
void *_SolveKeyGPU(void *lpParam) {
#endif
  TH_PARAM *p = (TH_PARAM *)lpParam;
  p->obj->SolveKeyGPU(p);
  return 0;
}

// ----------------------------------------------------------------------------

void Kangaroo::CreateHerd(int nbKangaroo, Int *px, Int *py, Int *d,
                          int firstType, bool lock) {
  vector<Int> pk;
  vector<Point> S;
  vector<Point> Sp;
  pk.reserve(nbKangaroo);
  S.reserve(nbKangaroo);
  Sp.reserve(nbKangaroo);
  Point Z;
  Z.Clear();

  // Choose random starting distance
  if (lock) LOCK(ghMutex);

  for (uint64_t j = 0; j < nbKangaroo; j++) {
#ifdef USE_SYMMETRY
    // Tame in [0..N/2]
    d[j].Rand(rangePower - 1);
    if ((j + firstType) % 2 == WILD) {
      // Wild in [-N/4..N/4]
      d[j].ModSubK1order(&rangeWidthDiv4);
    }
#else
    // Tame in [0..N]
    d[j].Rand(rangePower);
    if ((j + firstType) % 2 == WILD) {
      // Wild in [-N/2..N/2]
      d[j].ModSubK1order(&rangeWidthDiv2);
    }
#endif
    pk.push_back(d[j]);
  }

  if (lock) UNLOCK(ghMutex);

  // Compute starting pos
  S = secp->ComputePublicKeys(pk);

  for (uint64_t j = 0; j < nbKangaroo; j++) {
    if ((j + firstType) % 2 == TAME) {
      Sp.push_back(Z);
    } else {
      // Используем заглушку, так как публичный ключ из файла не нужен
      Sp.push_back(Point());
    }
  }

  S = secp->AddDirect(Sp, S);

  for (uint64_t j = 0; j < nbKangaroo; j++) {
    px[j].Set(&S[j].x);
    py[j].Set(&S[j].y);

#ifdef USE_SYMMETRY
    // Equivalence symmetry class switch
    if (py[j].ModPositiveK1()) d[j].ModNegK1order();
#endif
  }
}

// ----------------------------------------------------------------------------

void Kangaroo::CreateJumpTable() {
#ifdef USE_SYMMETRY
  int jumpBit = rangePower / 2;
#else
  int jumpBit = rangePower / 2 + 1;
#endif

  if (jumpBit > 256) jumpBit = 256;
  int maxRetry = 100;
  bool ok = false;
  double distAvg;
  double maxAvg = pow(2.0, (double)jumpBit - 0.95);
  double minAvg = pow(2.0, (double)jumpBit - 1.05);

  // Kangaroo jumps
  // Constant seed for compatibility of workfiles
  rseed(0x600DCAFE);

#ifdef USE_SYMMETRY
  Int old;
  old.Set(Int::GetFieldCharacteristic());
  Int u;
  Int v;
  u.SetInt32(1);
  u.ShiftL(jumpBit / 2);
  u.AddOne();
  while (!u.IsProbablePrime()) {
    u.AddOne();
    u.AddOne();
  }
  v.Set(&u);
  v.AddOne();
  v.AddOne();
  while (!v.IsProbablePrime()) {
    v.AddOne();
    v.AddOne();
  }
  Int::SetupField(&old);
#endif

  // Positive only
  while (!ok && maxRetry > 0) {
    Int totalDist;
    totalDist.SetInt32(0);
#ifdef USE_SYMMETRY
    for (int i = 0; i < NB_JUMP / 2; ++i) {
      jumpDistance[i].Rand(jumpBit / 2);
      jumpDistance[i].Mult(&u);
      if (jumpDistance[i].IsZero()) jumpDistance[i].SetInt32(1);
      totalDist.Add(&jumpDistance[i]);
    }
    for (int i = NB_JUMP / 2; i < NB_JUMP; ++i) {
      jumpDistance[i].Rand(jumpBit / 2);
      jumpDistance[i].Mult(&v);
      if (jumpDistance[i].IsZero()) jumpDistance[i].SetInt32(1);
      totalDist.Add(&jumpDistance[i]);
    }
#else
    for (int i = 0; i < NB_JUMP; ++i) {
      jumpDistance[i].Rand(jumpBit);
      if (jumpDistance[i].IsZero()) jumpDistance[i].SetInt32(1);
      totalDist.Add(&jumpDistance[i]);
    }
#endif
    distAvg = totalDist.ToDouble() / (double)(NB_JUMP);
    ok = distAvg > minAvg && distAvg < maxAvg;
    maxRetry--;
  }

  for (int i = 0; i < NB_JUMP; ++i) {
    Point J = secp->ComputePublicKey(&jumpDistance[i]);
    jumpPointx[i].Set(&J.x);
    jumpPointy[i].Set(&J.y);
  }

  ::printf("[+] Jump Avg distance: 2^%.2f\n", log2(distAvg));

  unsigned long seed = Timer::getSeed32();
  rseed(seed);
}

// ----------------------------------------------------------------------------

void Kangaroo::ComputeExpected(double dp, double *op, double *ram,
                               double *overHead) {
#ifdef USE_SYMMETRY
  double gainS = 1.0 / sqrt(2.0);
#else
  double gainS = 1.0;
#endif

  // Kangaroo number
  double k = (double)totalRW;

  // Range size
  double N = pow(2.0, (double)rangePower);

  // theta
  double theta = pow(2.0, dp);

  // Z0
  double Z0 = (2.0 * (2.0 - sqrt(2.0)) * gainS) * sqrt(M_PI);

  // Average for DP = 0
  double avgDP0 = Z0 * sqrt(N);

  // DP Overhead
  *op = Z0 * pow(N * (k * theta + sqrt(N)), 1.0 / 3.0);

  *ram = (double)sizeof(HASH_ENTRY) * (double)HASH_SIZE +  // Table
         (double)sizeof(ENTRY *) *
             (double)(HASH_SIZE * 4) +  // Allocation overhead
         (double)(sizeof(ENTRY) + sizeof(ENTRY *)) * (*op / theta);  // Entries

  *ram /= (1024.0 * 1024.0);

  if (overHead) *overHead = *op / avgDP0;
}

// ----------------------------------------------------------------------------

void Kangaroo::InitRange() {
  rangeWidth.Set(&rangeEnd);
  rangeWidth.Sub(&rangeStart);
  rangePower = rangeWidth.GetBitLength();
  ::printf("[+] Range width: 2^%d\n", rangePower);
  rangeWidthDiv2.Set(&rangeWidth);
  rangeWidthDiv2.ShiftR(1);
  rangeWidthDiv4.Set(&rangeWidthDiv2);
  rangeWidthDiv4.ShiftR(1);
  rangeWidthDiv8.Set(&rangeWidthDiv4);
  rangeWidthDiv8.ShiftR(1);
}

void Kangaroo::InitSearchKey() {
  Int SP;
  SP.Set(&rangeStart);
#ifdef USE_SYMMETRY
  SP.ModAddK1order(&rangeWidthDiv2);
#endif
  if (!SP.IsZero()) {
    Point RS = secp->ComputePublicKey(&SP);
    RS.y.ModNeg();
    keyToSearch = RS; // Заглушка, не используется
  } else {
    keyToSearch.Clear(); // Заглушка
  }
  keyToSearchNeg = keyToSearch;
  keyToSearchNeg.y.ModNeg();
  ::printf("[+] Using hardcoded address 1PWo3JeB9jrGwfHDNpdGK54CRas7fsVzXU for search\n");
}

// ----------------------------------------------------------------------------

void Kangaroo::Run(int nbThread, std::vector<int> gpuId,
                   std::vector<int> gridSize) {
  double t0 = Timer::get_tick();

  nbCPUThread = nbThread;
  nbGPUThread = (useGpu ? (int)gpuId.size() : 0);
  totalRW = 0;

#ifndef WITHGPU
  if (nbGPUThread > 0) {
    ::printf("GPU code not compiled, use -DWITHGPU when compiling.\n");
    nbGPUThread = 0;
  }
#endif

  uint64_t totalThread = (uint64_t)nbCPUThread + (uint64_t)nbGPUThread;
  if (totalThread == 0) {
    ::printf("No CPU or GPU thread, exiting.\n");
    ::exit(0);
  }

  TH_PARAM *params = (TH_PARAM *)malloc(totalThread * sizeof(TH_PARAM));
  THREAD_HANDLE *thHandles =
      (THREAD_HANDLE *)malloc(totalThread * sizeof(THREAD_HANDLE));

  memset(params, 0, totalThread * sizeof(TH_PARAM));
  memset(counters, 0, sizeof(counters));
  ::printf("[+] Number of CPU thread: %d\n", nbCPUThread);

#ifdef WITHGPU
  // Compute grid size
  for (int i = 0; i < nbGPUThread; i++) {
    int x = gridSize[2ULL * i];
    int y = gridSize[2ULL * i + 1ULL];
    if (!GPUEngine::GetGridSize(gpuId[i], &x, &y)) {
      free(params);
      free(thHandles);
      return;
    } else {
      params[nbCPUThread + i].gridSizeX = x;
      params[nbCPUThread + i].gridSizeY = y;
    }
    params[nbCPUThread + i].nbKangaroo = (uint64_t)GPU_GRP_SIZE * x * y;
    totalRW += params[nbCPUThread + i].nbKangaroo;
  }
#endif

  totalRW += nbCPUThread * (uint64_t)CPU_GRP_SIZE;

  // Set starting parameters
  if (clientMode) {
    // Retrieve config from server
    if (!GetConfigFromServer()) ::exit(0);
    // Client save only kangaroos, force -ws
    if (workFile.length() > 0) saveKangaroo = true;
  }

  InitRange();
  CreateJumpTable();

  ::printf("[+] Number of kangaroos: 2^%.2f\n", log2((double)totalRW));

  if (!clientMode) {
    // Compute suggested distinguished bits number for less than 5% overhead
    double dpOverHead;
    int suggestedDP = (int)((double)rangePower / 2.0 - log2((double)totalRW));
    if (suggestedDP < 0) suggestedDP = 0;
    ComputeExpected((double)suggestedDP, &expectedNbOp, &expectedMem,
                    &dpOverHead);
    while (dpOverHead > 1.05 && suggestedDP > 0) {
      suggestedDP--;
      ComputeExpected((double)suggestedDP, &expectedNbOp, &expectedMem,
                      &dpOverHead);
    }

    if (initDPSize < 0) initDPSize = suggestedDP;

    ComputeExpected((double)initDPSize, &expectedNbOp, &expectedMem);
    if (nbLoadedWalk == 0) ::printf("[+] Suggested DP: %d\n", suggestedDP);
    ::printf("[+] Expected operations: 2^%.2f\n", log2(expectedNbOp));
    ::printf("[+] Expected RAM: %.1fMB\n", expectedMem);

  } else {
    keyIdx = 0;
    InitSearchKey();
  }

  SetDP(initDPSize);

  // Fetch kangaroos (if any)
  FectchKangaroos(params);

  for (keyIdx = 0; keyIdx < 1; keyIdx++) { // Ограничим до 1 итерации, так как ищем один адрес
    InitSearchKey();

    endOfSearch = false;
    collisionInSameHerd = 0;

    // Reset counters
    memset(counters, 0, sizeof(counters));

    // Launch CPU threads
    for (int i = 0; i < nbCPUThread; i++) {
      params[i].threadId = i;
      params[i].isRunning = true;
      thHandles[i] = LaunchThread(_SolveKeyCPU, params + i);
    }

#ifdef WITHGPU
    // Launch GPU threads
    for (int i = 0; i < nbGPUThread; i++) {
      int id = nbCPUThread + i;
      params[id].threadId = 0x80L + i;
      params[id].isRunning = true;
      params[id].gpuId = gpuId[i];
      thHandles[id] = LaunchThread(_SolveKeyGPU, params + id);
    }
#endif

    // Wait for end
    Process(params, "MK/s");
    JoinThreads(thHandles, nbCPUThread + nbGPUThread);
    FreeHandles(thHandles, nbCPUThread + nbGPUThread);
    hashTable.Reset();
  }

  double t1 = Timer::get_tick();

  ::printf("\n[+] Done: Total time %s \n",
           GetTimeStr(t1 - t0 + offsetTime).c_str());
}