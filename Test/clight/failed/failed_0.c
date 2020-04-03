struct lock;
typedef struct lock lock;
struct lock {
  int wait;
  lock* next;
};

// There might be some bug in CompCertTSO compiler.
// Defining global variable lock caused stack overflow of compcertTSO
// This only happens when lock has a field of type lock* and there
// is a typedef naming "struct lock" to "lock"
lock lock;

// For example 
//struct lock;
//typedef struct lock lock;
//struct lock {
//  int wait;
//  struct lock* next;
//};
// won't fail.

int main() {
        return 0;
}