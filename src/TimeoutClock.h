#include <ctime>
#include <functional>

/**
 * Provides timeout function in cpu time in seconds.
 */
class TimeoutClock{
private:
    std::clock_t c_start;
    float timeoutInSeconds;
    std::clock_t deadline;

public:
    TimeoutClock(){};

    TimeoutClock(float timeoutInSeconds):
        c_start(std::clock())
    {
        setTimeout(timeoutInSeconds);
    }

    /**
     * Returns true if the deadline is reached.
     */
    bool timedOut() {
        if (std::clock() > deadline) {
            return true;
        } else {
            return false;
        }
    }

    void resetTimeout(){
        c_start = std::clock();
        deadline = c_start + timeoutInSeconds * CLOCKS_PER_SEC;
    }

    void setTimeout(float timeoutInSeconds) {
        this->timeoutInSeconds = timeoutInSeconds;
        resetTimeout();
    }

    std::function<int(void)> getTimeoutCallback(){
        std::function<int(void)> f =
            std::bind(&TimeoutClock::timedOut, this);
        return f;
    }
};
