#include <cstdlib>
#include <lld/Common/Driver.h>
#include <mutex>
#include <iostream>

using namespace llvm;

const char *alloc_str(const std::string &str) {
    size_t size = str.length();
    if (size > 0) {
        char *strPtr = reinterpret_cast<char *>(malloc(size + 1));
        memcpy(strPtr, str.c_str(), size + 1);
        return strPtr;
    }
    return nullptr;
}

// LLD seems not to be thread safe
std::mutex _wasmMutex;

extern "C" {
    struct LLDInvokeResult {
        bool success;
        const char *messages;
    };

    void link_free_result(LLDInvokeResult *result) {
        if (result->messages) {
            free(reinterpret_cast<void *>(const_cast<char *>(result->messages)));
        }
    }

    LLDInvokeResult lld_link(int argc, const char *const *argv) {
        std::string outputString, errorString;
        llvm::raw_string_ostream outputStream(outputString);
        llvm::raw_string_ostream errorStream(errorString);
        std::vector<const char *> args(argv, argv + argc);
        LLDInvokeResult result;
        std::unique_lock<std::mutex> lock(_wasmMutex);
        result.success = lld::wasm::link(args, false, outputStream, errorStream);
        std::string resultMessage = errorStream.str() + outputStream.str();
        result.messages = alloc_str(resultMessage);
        return result;
    }
}
