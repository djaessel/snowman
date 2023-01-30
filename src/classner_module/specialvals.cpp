#include "specialvals.h"

uint processorCount()
{
  uint processor_count = std::thread::hardware_concurrency();

  processor_count *= 0.75;
  if (processor_count <= 0)
    processor_count = 1;

  return processor_count;
}
